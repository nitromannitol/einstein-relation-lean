import EinsteinFull.Calculus.C10FirstUnitFluxSize
import EinsteinFull.Blueprint.G3.Proofs.C9DyadicIncrements
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import EinsteinFull.Calculus.C7EndpointUniformProjection
import EinsteinFull.Calculus.C4PhysicalForwardTimePrimitive
import EinsteinFull.Work.W6.PhysicalSemigroupWeakTimeRealizationProof
import EinsteinFull.Calculus.C8EndpointTransposeProjection
import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Calculus.C1CrudeEnergySupport
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Convolution

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The original local estimate supplies exactly the locality input used by
the dyadic argument, after discarding the moment and time-derivative bounds. -/
theorem c19_dyadic_locality_input_of_forced_local
    (hlocal : node_l_u3A_forced_u2D_localStmt) : node_e_u3A_forced_u2D_localityStmt := by
  intro d hd D
  obtain ⟨α, Cdet, c, N, hα, hCdet, hc, hp⟩ := hlocal d hd D
  obtain ⟨C, Cp, hC, hCp, h⟩ := hp 2 le_rfl
  refine ⟨Cdet, c, N, hCdet, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
  obtain ⟨G, V, hgrad, _, hloc, hbound⟩ := h Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
  exact ⟨G, fun t ht => ⟨(hgrad t ht).1, (hgrad t ht).2.1⟩, hloc, hbound⟩


/-- The meaning predicate fixes both the actual gradients and the literal
fluxes. An existential weak-equation producer therefore cannot select a
different flux from the one in the locality target. -/
theorem c19_finiteTimeFlux_unique
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F G' F' : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (hF' : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G' F') :
    G = G' ∧ F = F' := by
  have hG : G = G' := by
    funext t ν
    exact (hF.choose_spec.choose_spec.1 t ν).unique
      (hF'.choose_spec.choose_spec.1 t ν)
  subst G'
  refine ⟨rfl, ?_⟩
  funext t ν j
  apply Lp.ext
  exact (hF.choose_spec.choose_spec.2 t ν j).trans
    (hF'.choose_spec.choose_spec.2 t ν j).symm

/-- The actual flux gradient integrates to the gradient of the uncentered
time primitive. In particular, centering the forward endpoints introduces
no error term in the integrated conservative equation. -/
theorem c19_integrated_flux_gradient
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (ν : FluxIndex d) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ),
        uncenteredEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true))
          ζ P Pdag β a μ s.toNNReal)
      (fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν j) := by
  let := reducedLaw_probability Q
  have hc : Continuous (fun s : ℝ≥0 =>
      uncenteredEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true))
        ζ P Pdag β a μ s) := by
    cases ν with
    | inl i => exact hP.2.2.1 _
    | inr b => exact hPd.continuous_apply hP _
  intro j
  apply HasComplexHorizontalDerivative.integral_of_ae
    (hc.comp continuous_real_toNNReal).integrableOn_Icc
    ((hF.choose ν j).comp continuous_real_toNNReal).integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  cases ν with
  | inl i =>
    have he : G s.toNNReal (.inl i) = hP.gradientOrbit (β i + ζ • a ⟨0, by omega⟩ i) s :=
      (hF.choose_spec.choose_spec.1 s.toNNReal (.inl i)).unique
        (hP.centered_gradientOrbit_spec _ hspos)
    change HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (P s.toNNReal (β i + ζ • a ⟨0, by omega⟩ i)) (G s.toNNReal (.inl i) j)
    rw [congrFun he j]
    exact hP.gradientOrbit_spec _ hspos j
  | inr b => exact hF.choose_spec.choose_spec.1 s.toNNReal (.inr b) j

/-- The supplied time-flux theorem holds for the literal flux in this task,
by uniqueness, with no new weak-equation premise on that flux. -/
theorem c19_actual_flux_weak_identity
    (hflux : node_e_u3A_time_u2D_fluxStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (t : ℝ≥0) (v : Lp ℂ 2 (reducedLaw Q))
    (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∀ i : Fin d,
      (∫ ω, (P t (β i + ζ • a ⟨0, by omega⟩ i)) ω * v ω ∂reducedLaw Q) =
        -(1 / 2 : ℂ) * (∫ ω, ∑ j, F t (.inl i) j ω * V j ω ∂reducedLaw Q) +
          ζ * (∫ ω, F t (.inl i) ⟨0, by omega⟩ ω * v ω ∂reducedLaw Q)) ∧
    (∫ ω, (Pdag t (β ⟨0, by omega⟩)) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (∫ ω, ∑ j, F t (.inr ()) j ω * V j ω ∂reducedLaw Q) := by
  obtain ⟨G', F', hF', hw⟩ := hflux d hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd
  obtain ⟨rfl, rfl⟩ := c19_finiteTimeFlux_unique hd Q ζ P Pdag β a μ G F G' F' hF hF'
  exact hw t v V hv

/-- The conservative equation for an actual flux increment keeps both
endpoint traces and the forward force term. The transpose force is already
contained in the literal flux, so it contributes no separate scalar term. -/
theorem c19_actual_flux_increment_weak_identity
    (hflux : node_e_u3A_time_u2D_fluxStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (s t : ℝ≥0) (ν : FluxIndex d) (v : Lp ℂ 2 (reducedLaw Q))
    (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, (uncenteredEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true))
      ζ P Pdag β a μ t -
      uncenteredEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true))
        ζ P Pdag β a μ s) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (∫ ω, ∑ j, (F t ν j - F s ν j) ω * V j ω ∂reducedLaw Q) +
      ν.elim (fun _ => ζ * (∫ ω,
        (F t ν ⟨0, by omega⟩ - F s ν ⟨0, by omega⟩) ω * v ω ∂reducedLaw Q))
        (fun _ => 0) := by
  have hi (f w : Lp ℂ 2 (reducedLaw Q)) :
      Integrable (fun ω => f ω * w ω) (reducedLaw Q) :=
    (Lp.memLp f).integrable_mul (Lp.memLp w)
  have hpair (f g w : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, (f - g) ω * w ω ∂reducedLaw Q) =
        (∫ ω, f ω * w ω ∂reducedLaw Q) - ∫ ω, g ω * w ω ∂reducedLaw Q := by
    rw [← integral_sub (hi f w) (hi g w)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with ω hω
    simp only [hω, Pi.sub_apply, sub_mul]
  have hrow (A B : Fin d → Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, ∑ j, (A j - B j) ω * V j ω ∂reducedLaw Q) =
        (∫ ω, ∑ j, A j ω * V j ω ∂reducedLaw Q) -
          ∫ ω, ∑ j, B j ω * V j ω ∂reducedLaw Q := by
    rw [integral_finsetSum _ (fun j _ => hi (A j - B j) (V j)),
      integral_finsetSum _ (fun j _ => hi (A j) (V j)),
      integral_finsetSum _ (fun j _ => hi (B j) (V j))]
    simp_rw [hpair]
    simp only [Finset.sum_sub_distrib]
  have ht := c19_actual_flux_weak_identity hflux hd D Q hQ β a μ hβ ha hμ ζ P Pdag
    hP hPd G F hF t v V hv
  have hs := c19_actual_flux_weak_identity hflux hd D Q hQ β a μ hβ ha hμ ζ P Pdag
    hP hPd G F hF s v V hv
  rw [hpair, hrow]
  cases ν with
  | inl i =>
    simp only [Sum.elim_inl, uncenteredEndpoint]
    rw [hpair, ht.1 i, hs.1 i]
    ring
  | inr b =>
    cases b
    simp only [Sum.elim_inr, uncenteredEndpoint, transposeEndpoint]
    rw [ht.2, hs.2]
    ring

/-- On a retained interior the primitive of the supplied forward flux gradient
satisfies the actual difference equation. Both generator equations and the
retained physical gradient are supplied internally by the two semigroups. -/
theorem c19_forward_integrated_gradient_retained_interior
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (ν : Fin d) (t : ℝ≥0) :
    let f := β ν + ζ • a ⟨0, by omega⟩ ν
    let u := ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f
    let H := fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inl ν) j
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ O : Set (Vec d), MeasurableSet O → (∀ x ∈ O, χ x = 1) →
    ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
    IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
    (fun x => f (translate x ω)) =ᵐ[volume.restrict O] fr →
    let v := ∫ s in (0 : ℝ)..(t : ℝ), Pr s.toNNReal fr
    ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence O
        (fun x j => L ((1 / 2 : ℂ) * (∑ k, (ω.1 x j k : ℂ) *
          (H k (translate x ω) - K k x))))
        (fun x => L (((P t f) (translate x ω) - (Pr t fr) x) -
          ζ * (∑ j, (ω.1 x j ⟨0, by omega⟩ : ℂ) *
            (H j (translate x ω) - K j x)))) := by
  intro f u H
  have hG := c19_integrated_flux_gradient hd Q ζ P Pdag β a μ hP hPd G F hF (.inl ν) t
  have hU : (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f) = u := by
    exact integral_Icc_eq_integral_Ioc.trans
      (intervalIntegral.integral_of_le (f := fun s : ℝ => P s.toNNReal f)
        (μ := (volume : Measure ℝ)) t.coe_nonneg).symm
  simp only [Sum.elim_inl, uncenteredEndpoint] at hG
  change HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f) H at hG
  rw [hU] at hG
  have hres := short_time_actual_retained_spatial_residual Q (hP.generator_timeIntegral f t) hG
  have hsub := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (P t f - f)).measurable
    ((Lp.stronglyMeasurable (P t f)).measurable.sub (Lp.stronglyMeasurable f).measurable)
    (Lp.coeFn_sub (P t f) f)
  filter_upwards [hres, hsub] with ω hω hsω
  intro χ hχ O hO hplateau Pr hPr fr hinit v
  have hvg := physical_forward_generator_timeIntegral
    (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr hPr fr t
  obtain ⟨K, hK, hdiv⟩ := hω χ hχ v (Pr t fr - fr) hvg
  refine ⟨K, hK, fun L => ?_⟩
  apply (HasWeakDivergence.restrict_subset (Set.subset_univ O)
    MeasurableSet.univ (hdiv L)).congr_ae
  · filter_upwards [ae_restrict_mem hO] with x hx
    funext j
    have he := (ForcedLocality.retainedPair_eq_at χ ω (hplateau x hx)).1
    have hd := C9ShortTimeLocality.retainedDefects_eq_zero χ ω (hplateau x hx)
      (fun k => H k (translate x ω)) ⟨0, by omega⟩ ζ
    simp only [he, hd.1 j, add_zero]
  · filter_upwards [ae_restrict_of_ae hsω,
      ae_restrict_of_ae (Lp.coeFn_sub (Pr t fr) fr), hinit,
      ae_restrict_mem hO] with x hs hr hi hx
    have he := (ForcedLocality.retainedPair_eq_at χ ω (hplateau x hx)).1
    have hd := C9ShortTimeLocality.retainedDefects_eq_zero χ ω (hplateau x hx)
      (fun k => H k (translate x ω)) ⟨0, by omega⟩ ζ
    simp only [Pi.sub_apply] at hs hr
    rw [hs, hr, hi, hd.2, he]
    congr 1
    ring

/-- Gaussian coercivity for the primitive of the supplied forward gradient.
The stationary and physical generator graphs follow from the actual semigroups;
no comparison estimate or weighted admissibility is assumed. -/
theorem c19_forward_integrated_gradient_gaussian_coercivity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (ν : Fin d) (t : ℝ≥0) :
    let f := β ν + ζ • a ⟨0, by omega⟩ ν
    let u := ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f
    let H := fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inl ν) j
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ χ : C(Vec d, ℝ), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
    IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
    let v := ∫ s in (0 : ℝ)..(t : ℝ), Pr s.toNNReal fr
    ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let e : Vec d → ℂ := fun x => u (translate x ω) - v x
      let J : Fin d → Vec d → ℂ := fun j x => H j (translate x ω) - K j x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ∧
      Integrable (fun x => W x * ‖e x‖ ^ 2) ∧
      2 * (∫ x, ((P t f - f) (translate x ω) - (Pr t fr - fr) x) *
          (((η x ^ 2 : ℝ) : ℂ) * star (e x))).re +
        (∫ x, W x * ‖e x‖ ^ 2) +
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ≤
      (16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1) * (∫ x, η x ^ 2 * ‖e x‖ ^ 2) +
      (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j,
        ‖C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => H k (translate x ω)) j‖ ^ 2) +
      (∫ x, η x ^ 2 *
        ‖C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => H k (translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2) := by
  intro f u H Λ
  have hG := c19_integrated_flux_gradient hd Q ζ P Pdag β a μ hP hPd G F hF (.inl ν) t
  have hU : (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f) = u := by
    exact integral_Icc_eq_integral_Ioc.trans
      (intervalIntegral.integral_of_le (f := fun s : ℝ => P s.toNNReal f)
        (μ := (volume : Measure ℝ)) t.coe_nonneg).symm
  simp only [Sum.elim_inl, uncenteredEndpoint] at hG
  change HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f) H at hG
  rw [hU] at hG
  filter_upwards [short_time_actual_retained_gaussian_coercivity hd Q
    (hP.generator_timeIntegral f t) hG] with ω hω
  intro χ hχ Pr hPr fr v
  exact hω χ hχ v (Pr t fr - fr)
    (physical_forward_generator_timeIntegral
      (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr hPr fr t)

/-- The transpose primitive's retained interior equation uses the literal
integrated gradient from the supplied finite-time flux. The cutoff bounds
supply the retained coefficient admissibility internally. -/
theorem c19_transpose_integrated_gradient_retained_interior
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F) (t : ℝ≥0) :
    let f := β ⟨0, by omega⟩
    let u := ∫ s in (0 : ℝ)..(t : ℝ), Pdag s.toNNReal f
    let H := fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inr ()) j
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ O : Set (Vec d), MeasurableSet O → (∀ x ∈ O, χ x = 1) →
    ∀ (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
    IsPhysicalComplexTransposeSemigroup
      (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr Tr →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
    (fun x => f (translate x ω)) =ᵐ[volume.restrict O] fr →
    let v := ∫ s in (0 : ℝ)..(t : ℝ), Tr s.toNNReal fr
    ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence O
        (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
          (H k (translate x ω) - K k x)) -
          2 * ζ * (ω.1 x j ⟨0, by omega⟩ : ℂ) * (u (translate x ω) - v x)))
        (fun x => L (2 * ((Pdag t f) (translate x ω) - (Tr t fr) x))) := by
  intro f u H
  have hG := c19_integrated_flux_gradient hd Q ζ P Pdag β a μ hP hPd G F hF (.inr ()) t
  have hU : (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal f) = u := by
    exact integral_Icc_eq_integral_Ioc.trans
      (intervalIntegral.integral_of_le (f := fun s : ℝ => Pdag s.toNNReal f)
        (μ := (volume : Measure ℝ)) t.coe_nonneg).symm
  simp only [Sum.elim_inr, uncenteredEndpoint, transposeEndpoint] at hG
  change HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal f) H at hG
  rw [hU] at hG
  obtain ⟨H', hH', hres⟩ := short_time_transpose_integral_retained_interior
    hd Q ⟨0, by omega⟩ ζ P Pdag hP hPd f t
  have hH : H' = H := hH'.unique hG
  rw [hH] at hres
  filter_upwards [hres, c4_ae_reduced_physical_elliptic Q] with ω hω hA
  intro χ hχ O hO hplateau Pr Tr hTr fr hinit v
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
  exact hω χ O hO hplateau hr Pr Tr hTr fr hinit

/-- Gaussian coercivity for the actual transpose time primitive. The stationary
part uses the supplied finite-time flux gradient, and the retained primitive
supplies its physical H1 graph. All weighted integrability follows internally. -/
theorem c19_transpose_integrated_gradient_gaussian_coercivity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F) (t : ℝ≥0) :
    let f := β ⟨0, by omega⟩
    let u := ∫ s in (0 : ℝ)..(t : ℝ), Pdag s.toNNReal f
    let H := fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inr ()) j
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)), (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
    IsPhysicalComplexTransposeSemigroup
      (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr Tr →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
    let v := ∫ s in (0 : ℝ)..(t : ℝ), Tr s.toNNReal fr
    ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let e : Vec d → ℂ := fun x => u (translate x ω) - v x
      let J : Fin d → Vec d → ℂ := fun j x => H j (translate x ω) - K j x
      let R : Fin d → Vec d → ℂ := fun j x => (1 / 2 : ℂ) *
        (∑ k, ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x k j : ℝ) : ℂ) * K k x) -
        ζ * ((ω.1 x j ⟨0, by omega⟩ -
          (ForcedLocality.retainedPair χ ω).1 x j ⟨0, by omega⟩ : ℝ) : ℂ) * v x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ∧
      Integrable (fun x => W x * ‖e x‖ ^ 2) ∧
      2 * (∫ x, ((Pdag t f - f) (translate x ω) - (Tr t fr - fr) x) *
          (((η x ^ 2 : ℝ) : ℂ) * star (e x))).re +
        (∫ x, W x * ‖e x‖ ^ 2) +
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ≤
      (4 * Λ + 16 / L) * (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) *
        (∫ x, η x ^ 2 * ‖e x‖ ^ 2) +
      (2 * (4 * Λ + 16 / L)) * (∫ x, η x ^ 2 * ∑ j, ‖R j x‖ ^ 2) := by
  intro f u H Λ
  letI : Fact (2 ≤ d) := ⟨hd⟩
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hG := c19_integrated_flux_gradient hd Q ζ P Pdag β a μ hP hPd G F hF (.inr ()) t
  have hU : (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal f) = u := by
    exact integral_Icc_eq_integral_Ioc.trans
      (intervalIntegral.integral_of_le (f := fun s : ℝ => Pdag s.toNNReal f)
        (μ := (volume : Measure ℝ)) t.coe_nonneg).symm
  simp only [Sum.elim_inr, uncenteredEndpoint, transposeEndpoint] at hG
  change HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal f) H at hG
  rw [hU] at hG
  obtain ⟨H', hH', hres⟩ := short_time_transpose_generator_retained_residual
    hd Q ⟨0, by omega⟩ ζ u (Pdag t f - f)
    (short_time_stationary_transpose_integral_generator Q ⟨0, by omega⟩ ζ P Pdag hP hPd f t)
  have hH : H' = H := hH'.unique hG
  rw [hH] at hres
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hΛ1 : 1 ≤ Λ := by
    have hexp := Real.one_le_exp (show 0 ≤ 2 * Λ₀ by
      nlinarith [Q.ellipticity_parameter])
    dsimp only [Λ]
    nlinarith [Q.ellipticity_parameter]
  filter_upwards [hres, hG.ae_reduced_spatial Q, c4_ae_reduced_physical_elliptic Q,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q) (reducedLaw_stationary Q) u,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q) (reducedLaw_stationary Q)
      (Pdag t f - f),
    ae_all_iff.mpr (fun j => ae_stationary_spatial_orbit_gaussian_memLp d hd
      (reducedLaw Q) (reducedLaw_stationary Q) (H j))]
    with ω hω hsp hA hu hq hGrad
  intro χ hχ Pr Tr hTr fr v
  have hvg := physical_transpose_generator_timeIntegral
    (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr Tr hTr fr t
  have hKex := hvg
  obtain ⟨K, hK, _⟩ := hKex
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
  have hb (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
    convert (hc.fun_mul (ha j k)).add
      (((memLp_top_const (1 : ℂ) : MemLp (fun _ : Vec d => (1 : ℂ)) ∞ volume).sub hc).mul_const
        ((1 : Mat d) j k : ℂ)) using 1
    funext x
    simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Pi.add_apply, Pi.sub_apply]
  refine ⟨K, hK, fun L r hL hr => ?_⟩
  intro e J R η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / (4 * L * r)) : ℂ)
  have hw : MemLp w ∞ volume := by
    have hc' : Continuous w := by dsimp only [w, euclideanSq, dot]; fun_prop
    apply memLp_top_of_bound hc'.aestronglyMeasurable 1
    refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (euclideanSq_nonneg_coords x))
        (by positivity))
  have hwp (z : Lp ℂ 2 (volume : Measure (Vec d))) :
      MemLp (fun x => w x * z x) 2 volume := hw.fun_mul (Lp.memLp z)
  have hwe : MemLp (fun x => w x * e x) 2 volume := by
    simpa only [e, w, mul_sub, Pi.sub_def] using (hu (4 * L * r) (by positivity)).sub (hwp v)
  have hwq : MemLp (fun x => w x *
      ((Pdag t f - f) (translate x ω) - (Tr t fr - fr) x)) 2 volume := by
    simpa only [w, mul_sub, Pi.sub_def] using
      (hq (4 * L * r) (by positivity)).sub (hwp (Tr t fr - fr))
  have hwJ (j : Fin d) : MemLp (fun x => w x * J j x) 2 volume := by
    simpa only [J, w, mul_sub, Pi.sub_def] using
      (hGrad j (4 * L * r) (by positivity)).sub (hwp (K j))
  have hwR (j : Fin d) : MemLp (fun x => w x * R j x) 2 volume := by
    convert ((memLp_finsetSum Finset.univ (fun k _ =>
      ((ha j k).sub (hb k j)).fun_mul (r := (2 : ℝ≥0∞)) (hwp (K k)))).const_mul
        (1 / 2 : ℂ)).sub
      ((((ha j ⟨0, by omega⟩).sub (hb j ⟨0, by omega⟩)).fun_mul
        (r := (2 : ℝ≥0∞)) (hwp v)).const_mul ζ) using 1
    funext x
    simp only [R, Pi.sub_apply, smul_eq_mul, Complex.ofReal_sub]
    rw [mul_sub, ← mul_assoc, mul_comm (w x) (1 / 2 : ℂ), mul_assoc,
      Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    · ring
  have hre j : HasWeakPartialDerivative univ j (fun x => (e x).re)
      (fun x => (J j x).re) := by
    simpa only [e, J, Complex.sub_re] using
      Correctors.hasWeakPartialDerivative_sub (hsp.1 j) (hK.1 j)
  have him j : HasWeakPartialDerivative univ j (fun x => (e x).im)
      (fun x => (J j x).im) := by
    simpa only [e, J, Complex.sub_im] using
      Correctors.hasWeakPartialDerivative_sub (hsp.2.1 j) (hK.2 j)
  have hdiv := hω (ForcedLocality.retainedPair χ ω).1 hb v (Tr t fr - fr) K hK hvg
  exact short_time_transpose_residual_gaussian_energy (fun x => ω.1 x) ⟨0, by omega⟩ ζ
    ha (ae_of_all _ (s5Elliptic_of_isElliptic hΛ1 hA))
    e (fun x => (Pdag t f - f) (translate x ω) - (Tr t fr - fr) x) J R hre him
    (by simpa only [e, J, R, Complex.reCLM_apply] using hdiv Complex.reCLM)
    (by simpa only [e, J, R, Complex.imCLM_apply] using hdiv Complex.imCLM)
    hΛ hL hr hwe hwq hwJ hwR

/-- The deterministic bound from the original forced-local statement applies
to the literal gradient supplied with the finite-time flux, including at
positive times below one. The locality clause is not used here. -/
theorem c19_actual_gradient_deterministic_bound
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ Cdet : ℝ, ∃ N : ℕ, 1 ≤ Cdet ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 4 →
    ∀ (ν : FluxIndex d) (t : ℝ≥0), 0 < (t : ℝ) → ∀ᵐ ω ∂reducedLaw Q,
      Real.sqrt (∑ j : Fin d, ‖G t ν j ω‖ ^ 2) ≤
        Cdet * (2 + (t : ℝ)) ^ N * Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  obtain ⟨α, Cdet, c, N, _, hCdet, _, hdata⟩ := hlocal d hd D
  obtain ⟨C, Cp, _, _, hdata⟩ := hdata 2 le_rfl
  refine ⟨Cdet, N, hCdet, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν t ht
  let κ : EndpointIndex d := ν.elim Sum.inl (fun _ => Sum.inr true)
  obtain ⟨G', V, hg, _, _, hdet⟩ := hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd κ
  have he : G' t = G t ν := (hg t ht).1.unique (hF.choose_spec.choose_spec.1 t ν)
  filter_upwards [hdet t ht hζ] with ω hω
  rw [he] at hω
  exact (le_add_of_nonneg_left (norm_nonneg _)).trans hω


/-- The literal primitive of every supplied flux-gradient coordinate is
uniformly essentially bounded on the first unit interval. The factor two is
from the finite-measure L2 Bochner-integral estimate. -/
theorem c19_first_unit_integrated_gradient_deterministic_bound
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ M : ℝ, 0 < M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 2 →
    ∀ (ν : FluxIndex d) (t : ℝ≥0), (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ j : Fin d, ‖(∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν j) ω‖ ≤ M := by
  obtain ⟨A, N, hA, hbound⟩ := c19_actual_gradient_deterministic_bound hlocal d hd D
  let B := A * 3 ^ N * Real.exp (4 * A)
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨2 * B, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν t ht
  let := reducedLaw_probability Q
  have htime (j : Fin d) : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      ∀ᵐ ω ∂reducedLaw Q, ‖G s.toNNReal ν j ω‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hscoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1
    have hb := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF
      (hζ.trans (by norm_num)) ν s.toNNReal (by simpa only [hscoe] using hspos)
    have hpow : (2 + s) ^ N ≤ (3 : ℝ) ^ N :=
      pow_le_pow_left₀ (by linarith) (by linarith [hs.2]) N
    have hzsq : ‖ζ‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg ζ]
    have hzs : ‖ζ‖ ^ 2 * s ≤ 4 :=
      (mul_le_mul_of_nonneg_left (hs.2.trans ht) (sq_nonneg _)).trans (by simpa using hzsq)
    have hexp : Real.exp (A * ‖ζ‖ ^ 2 * s) ≤ Real.exp (4 * A) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = A * (‖ζ‖ ^ 2 * s) := by ring
        _ ≤ A * 4 := mul_le_mul_of_nonneg_left hzs hAp.le
        _ = _ := mul_comm _ _
    filter_upwards [hb] with ω hω
    have hsingle : ‖G s.toNNReal ν j ω‖ ≤
        Real.sqrt (∑ k : Fin d, ‖G s.toNNReal ν k ω‖ ^ 2) :=
      (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)).mpr
        (Finset.single_le_sum
          (f := fun k : Fin d => ‖G s.toNNReal ν k ω‖ ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ j))
    apply hsingle.trans (hω.trans ?_)
    rw [hscoe]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hAp.le) hexp
      (Real.exp_nonneg _) (by positivity)
  have hprim (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ‖(∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν j) ω‖ ≤ 2 * B := by
    have hi : IntegrableOn (fun s : ℝ => G s.toNNReal ν j)
        (Icc (0 : ℝ) (t : ℝ)) volume :=
      ((hF.choose ν j).comp continuous_real_toNNReal).integrableOn_Icc
    have hb := UnitInitialization.ae_norm_integral_Lp_le hi (htime j)
    have hm : (volume.restrict (Icc (0 : ℝ) (t : ℝ))).real univ = (t : ℝ) := by
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        sub_zero, ENNReal.toReal_ofReal t.coe_nonneg]
    rw [hm] at hb
    filter_upwards [hb] with ω hω
    exact hω.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hB.le])
  exact ae_all_iff.mpr hprim


private theorem c19_integrable_gaussian {d : ℕ} {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
  have hp : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-κ * x j ^ 2))
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hκ)
  convert hp using 1
  funext x
  rw [← Real.exp_sum]
  congr 1
  simp only [euclideanSq, dot, ← Finset.mul_sum, sq]

/-- The actual integrated gradient supplies its own Gaussian integrability
and exponentially small retained forcing, with structural constants before
the law. Both the coefficient and clock belong to the retained joint field. -/
theorem c19_first_unit_integrated_gradient_retained_forcing
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 2 →
    ∀ (ν : FluxIndex d) (t : ℝ≥0), (t : ℝ) ≤ 1 →
    let H := fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν j
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (κ ρ : ℝ), 0 < κ → 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ → χ x = 1) →
      Integrable (fun x =>
        (∑ j : Fin d, Real.exp (-κ * euclideanSq x) *
          ‖C9ShortTimeLocality.retainedFluxDefect χ ω x
            (fun k => H k (translate x ω)) j‖ ^ 2) +
        Real.exp (-κ * euclideanSq x) *
          ‖C9ShortTimeLocality.retainedDriftDefect χ ω x
            (fun k => H k (translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2) ∧
      (∫ x,
        (∑ j : Fin d, Real.exp (-κ * euclideanSq x) *
          ‖C9ShortTimeLocality.retainedFluxDefect χ ω x
            (fun k => H k (translate x ω)) j‖ ^ 2) +
        Real.exp (-κ * euclideanSq x) *
          ‖C9ShortTimeLocality.retainedDriftDefect χ ω x
            (fun k => H k (translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2) ≤
        C * Real.exp (-(κ / 2) * ρ ^ 2) *
          (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x)) := by
  obtain ⟨M, hM, hprimitive⟩ :=
    c19_first_unit_integrated_gradient_deterministic_bound hlocal d hd D
  obtain ⟨A, hA, hforce⟩ := exists_retained_forcing_energy d D 2 (by norm_num)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  refine ⟨(A + 1) * (d : ℝ) * M ^ 2, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν t ht H
  let := reducedLaw_probability Q
  have hb := hprimitive Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν t ht
  have hsp : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d, ∀ᵐ x ∂volume,
      ‖H j (translate x ω)‖ ≤ M := by
    apply ae_all_iff.mpr
    intro j
    exact ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (H j)).measurable.norm (hb.mono fun ω hω => hω j)
  filter_upwards [hforce Q, hsp] with ω hf hω
  intro χ κ ρ hκ hρ hχ hχone
  have hG (j : Fin d) : Measurable (fun x => H j (translate x ω)) :=
    (Lp.stronglyMeasurable (H j)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hw : Measurable (fun x : Vec d => Real.exp (-(κ / 2) * euclideanSq x)) := by
    unfold euclideanSq dot
    fun_prop
  have hgauss := c19_integrable_gaussian (d := d) (show 0 < κ / 2 by positivity)
  have hGi (j : Fin d) : Integrable (fun x =>
      Real.exp (-(κ / 2) * euclideanSq x) * ‖H j (translate x ω)‖ ^ 2) := by
    apply (hgauss.mul_const (M ^ 2)).mono'
      (hw.mul ((hG j).norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [hω j] with x hx
    change ‖Real.exp (-(κ / 2) * euclideanSq x) * ‖H j (translate x ω)‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (Real.exp_nonneg _)
  have hbint (j : Fin d) :
      (∫ x, Real.exp (-(κ / 2) * euclideanSq x) * ‖H j (translate x ω)‖ ^ 2) ≤
        M ^ 2 * (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x)) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hGi j) (hgauss.const_mul _)
    filter_upwards [hω j] with x hx
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2)
        (Real.exp_nonneg (-(κ / 2) * euclideanSq x))
  have hsum : (∑ j : Fin d, ∫ x,
      Real.exp (-(κ / 2) * euclideanSq x) * ‖H j (translate x ω)‖ ^ 2) ≤
      (d : ℝ) * M ^ 2 * (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x)) := by
    calc
      _ ≤ ∑ _j : Fin d, M ^ 2 *
          (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x)) :=
        Finset.sum_le_sum fun j _ => hbint j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring
  obtain ⟨hi, he⟩ := hf χ κ ρ hκ hρ hχ hχone
    (fun j x => H j (translate x ω)) (fun j => (hG j).aestronglyMeasurable)
    hGi ⟨0, by omega⟩ ζ hζ
  refine ⟨hi, he.trans ?_⟩
  have hI : 0 ≤ ∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x) :=
    integral_nonneg fun _ => Real.exp_nonneg _
  calc
    _ ≤ A * Real.exp (-(κ / 2) * ρ ^ 2) *
        ((d : ℝ) * M ^ 2 * (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x))) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (Real.exp_nonneg _))
    _ = A * ((d : ℝ) * M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x))) := by ring
    _ ≤ (A + 1) * ((d : ℝ) * M ^ 2 * Real.exp (-(κ / 2) * ρ ^ 2) *
        (∫ x : Vec d, Real.exp (-(κ / 2) * euclideanSq x))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

private theorem c19_finite_integral_sq_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {u : X → ℂ} (hu : MemLp u 2 μ) :
    ‖∫ x, u x ∂μ‖ ^ 2 ≤ μ.real Set.univ * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hc : MemLp (fun _ : X => (1 : ℂ)) 2 μ := memLp_const _
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hc) (by simpa using hu)
  simp only [norm_one, one_mul, Real.rpow_two, integral_const, smul_eq_mul,
    mul_one, one_pow, ← Real.sqrt_eq_rpow] at h
  have hn := norm_integral_le_integral_norm (μ := μ) u
  have hI : 0 ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hs := Real.sq_sqrt hI
  have ht' := Real.sq_sqrt (measureReal_nonneg (μ := μ) (s := Set.univ))
  have hp := mul_nonneg (Real.sqrt_nonneg (μ.real Set.univ))
    (Real.sqrt_nonneg (∫ x, ‖u x‖ ^ 2 ∂μ))
  have hsq := sq_le_sq₀ (norm_nonneg _) hp |>.mpr (hn.trans h)
  simpa only [mul_pow, ht', hs] using hsq

private theorem c19_primitive_sq_bound {u : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) t))) :
    ‖∫ s in Icc (0 : ℝ) t, u s‖ ^ 2 ≤
      t * ∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2 := by
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_zero, ENNReal.toReal_ofReal ht] using c19_finite_integral_sq_bound hu

/-- Temporal integration preserves a uniform squared L2 error on the first
unit interval. This applies to a Gaussian-weighted difference of coherent
stationary and retained representatives. -/
theorem c19_first_unit_spacetime_primitive_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {u : ℝ × X → ℂ} (hu : Measurable u) {t B : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hB : 0 ≤ B)
    (hI : Integrable (fun p => ‖u p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) t)).prod μ))
    (hb : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
      (∫ x, ‖u (s, x)‖ ^ 2 ∂μ) ≤ B) :
    Integrable (fun x => ‖∫ s in Icc (0 : ℝ) t, u (s, x)‖ ^ 2) μ ∧
      (∫ x, ‖∫ s in Icc (0 : ℝ) t, u (s, x)‖ ^ 2 ∂μ) ≤ B := by
  have hm : Measurable (fun x => ∫ s in Icc (0 : ℝ) t, u (s, x)) :=
    (hu.stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Icc (0 : ℝ) t))).measurable
  have hpoint : ∀ᵐ x ∂μ, ‖∫ s in Icc (0 : ℝ) t, u (s, x)‖ ^ 2 ≤
      t * ∫ s in Icc (0 : ℝ) t, ‖u (s, x)‖ ^ 2 := by
    filter_upwards [hI.prod_left_ae] with x hx
    exact c19_primitive_sq_bound ht0
      ((memLp_two_iff_integrable_sq_norm
        (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx)
  have hi : Integrable (fun x => ‖∫ s in Icc (0 : ℝ) t, u (s, x)‖ ^ 2) μ := by
    apply (hI.integral_prod_right.const_mul t).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, t * (∫ s in Icc (0 : ℝ) t, ‖u (s, x)‖ ^ 2) ∂μ :=
      integral_mono_ae hi (hI.integral_prod_right.const_mul t) hpoint
    _ = t * ∫ s in Icc (0 : ℝ) t, ∫ x, ‖u (s, x)‖ ^ 2 ∂μ := by
      rw [integral_const_mul, ← integral_integral_swap hI]
    _ ≤ t * ∫ _s in Icc (0 : ℝ) t, B :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hI.integral_prod_left
        (integrable_const _) hb) ht0
    _ = t * (t * B) := by
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht0, smul_eq_mul]
    _ ≤ t * B := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ht1 (mul_nonneg ht0 hB)
    _ ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hB

private theorem c19_integral_joint_l2_trace {T X : Type*}
    [MeasurableSpace T] [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × X → ℂ} (hU : Measurable U)
    (heq : ∀ s, (fun x => U (s, x)) =ᵐ[μ] u s) :
    ∀ᵐ x ∂μ, Integrable (fun s => U (s, x)) ν ∧
      (∫ s, u s ∂ν) x = ∫ s, U (s, x) ∂ν := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro K _ hK
  obtain ⟨hi, he⟩ := short_time_coeFn_integral_joint_l2_local hu hU heq K hK.ne
  filter_upwards [hi.prod_left_ae, he] with x hx he
  exact ⟨hx, he⟩

private theorem c19_gaussian_weight_memLp {d : ℕ} {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * f x) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := 1) (by
    have hw : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / L) : ℂ)) := by
      dsimp only [euclideanSq, dot]
      fun_prop
    exact (hw.mul (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable)
  filter_upwards with x
  change ‖(Real.exp (-euclideanSq x / L) : ℂ) * f x‖ ≤ 1 * ‖f x‖
  have hq : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
  have hw : Real.exp (-euclideanSq x / L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hL.le)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul] using
    mul_le_mul_of_nonneg_right hw (norm_nonneg (f x))

/-- The literal forward and clock time primitives inherit the actual
retained Gaussian decay. All analytic integrability and trace conditions
are obtained from the two semigroups and their coherent representatives. -/
theorem c19_forward_clock_primitive_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ 2 →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
    let u := ∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
    ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
    let v := ∫ s in Icc (0 : ℝ) (t : ℝ), Pr s.toNNReal fr
    Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖u (translate x ω) - v x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖u (translate x ω) - v x‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2) := by
  intro Λ
  obtain ⟨L, K, c, hscale, hL, hK, hc, hdec⟩ :=
    short_time_forward_clock_actual_gaussian_decay_common_event d hd D 2 (by norm_num)
  refine ⟨L, K, c, hscale, hL, hK, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f t ht u
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hgen : ∃ g, IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g := by
    cases ν with
    | inl j =>
      obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ j
      obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
        hQ ha ⟨0, by omega⟩ j
      exact ⟨b + ζ • c, hb.add (hc.smul ζ)⟩
    | inr z =>
      obtain ⟨c, hc⟩ := centeredEquations_clock_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
      exact ⟨ζ • c, hc.smul ζ⟩
  obtain ⟨g, hfg⟩ := hgen
  obtain ⟨F, U, hF, hU, heF, heU, hprimitive⟩ := short_time_stationary_joint_primitive hP hfg
  have hfi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)
  have hIstat := integrable_sq_joint_l2_representative
    (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := (t : ℝ)))) hF heF
  filter_upwards [hdec Q hQ β a μ hβ ha hμ ζ hζ P hP ν g F U hF hU heF heU hprimitive,
    short_time_stationary_primitive_gaussian_strong_continuous hd Q hP f g F U hU heU hprimitive,
    short_time_stationary_physical_gaussian_energy_continuous hd Q hP f g F U hU heU hprimitive,
    ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF hIstat,
    ae_spatial_coeFn_integral_joint_l2_representative (reducedLaw Q)
      (reducedLaw_stationary Q) hfi hF heF] with ω hdecω hmem hcont htime htrace
  intro χ ρ hρ hχ hcompact hin fr hfr Pr hPr v
  obtain ⟨V, hV, heV⟩ := short_time_physical_evolution_joint_representative hPr fr
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  let E : ℝ × Vec d → ℂ := fun p => w p.2 * (F (p.1, translate p.2 ω) - V p)
  have hw : Measurable w := by dsimp only [w, euclideanSq, dot]; fun_prop
  have hsp : Measurable (fun p : ℝ × Vec d => F (p.1, translate p.2 ω)) :=
    hF.comp (measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const)))
  have hE : Measurable E := (hw.comp measurable_snd).mul (hsp.sub hV)
  have hEm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      MemLp (fun x => E (s, x)) 2 volume := by
    have hmV := (c19_gaussian_weight_memLp hL (Pr s.toNNReal fr)).ae_eq
      ((heV s).symm.mono fun x hx => congrArg (fun z : ℂ => w x * z) hx)
    simpa only [E, w, mul_sub, Pi.sub_def] using ((hmem L hL).1 s hs).sub hmV
  have henergy (s : ℝ) : (∫ x, ‖E (s, x)‖ ^ 2) =
      ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (s, translate x ω) - V (s, x)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [E, w, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hIE : Integrable (fun p => ‖E p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod volume) := by
    apply (integrable_prod_iff (hE.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact (hEm s ⟨hs.1, hs.2.trans ht⟩).norm.integrable_sq
    · have hi : IntegrableOn (fun s : ℝ => ∫ x,
          Real.exp (-euclideanSq x / L) ^ 2 *
            ‖F (s, translate x ω) - V (s, x)‖ ^ 2)
          (Icc (0 : ℝ) (t : ℝ)) :=
        ((hcont L hL (ForcedLocality.retainedPair χ ω).1 Pr hPr fr V heV).mono
          (Icc_subset_Icc le_rfl ht)).integrableOn_compact isCompact_Icc
      apply hi.congr
      filter_upwards with s
      simp only [Real.norm_of_nonneg (sq_nonneg _), henergy]
  have hbound : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      (∫ x, ‖E (s, x)‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [henergy]
    exact hdecω χ ρ hρ hχ hcompact hin fr hfr Pr hPr V heV s ⟨hs.1, hs.2.trans ht⟩
  obtain ⟨hi, hb⟩ := c19_first_unit_spacetime_primitive_bound volume hE
    t.coe_nonneg ht (by positivity) hIE hbound
  have hVtrace := c19_integral_joint_l2_trace
    (integrableOn_comp_toNNReal_Icc _ (hPr.2.2.1 fr) (t : ℝ)) hV heV
  have heq : (fun x => ‖∫ s in Icc (0 : ℝ) (t : ℝ), E (s, x)‖ ^ 2) =ᵐ[volume]
      (fun x => Real.exp (-euclideanSq x / L) ^ 2 * ‖u (translate x ω) - v x‖ ^ 2) := by
    filter_upwards [htrace, hVtrace, (htime L hL).norm.integrable_sq.prod_left_ae]
      with x hx hv htx
    have hMF : MemLp (fun s => w x * F (s, translate x ω)) 2
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) :=
      (memLp_two_iff_integrable_sq_norm
        ((measurable_const.mul (hsp.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)).mpr htx
    have hFint : IntegrableOn (fun s => F (s, translate x ω)) (Icc (0 : ℝ) (t : ℝ)) := by
      have hwi : w x ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
      apply ((hMF.integrable (by norm_num)).const_mul (w x)⁻¹).congr
      filter_upwards with s
      exact inv_mul_cancel_left₀ hwi _
    have he : (∫ s in Icc (0 : ℝ) (t : ℝ), E (s, x)) =
        w x * (u (translate x ω) - v x) := by
      dsimp only [E]
      rw [integral_const_mul, integral_sub hFint hv.1, ← hx, ← hv.2]
    rw [he, norm_mul, mul_pow]
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨hi.congr heq, ?_⟩
  rw [← integral_congr_ae heq]
  exact hb

private theorem c19_convolution_weak_partial {d : ℕ}
    {f g ζ : Vec d → ℝ} {j : Fin d}
    (hfg : HasWeakPartialDerivative Set.univ j f g)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (x : Vec d) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] coordinateDerivative j ζ) x =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) x := by
  have htest : IsSpatialTest Set.univ (fun z => ζ (x - z)) := by
    refine ⟨hζ.comp (contDiff_const.sub contDiff_id), ?_, Set.subset_univ _⟩
    exact hζc.comp_homeomorph (Homeomorph.subLeft x)
  have hder (z : Vec d) : coordinateDerivative j (fun w => ζ (x - w)) z =
      -coordinateDerivative j ζ (x - z) := by
    have h := ((hζ.differentiable (by simp) (x - z)).hasFDerivAt).comp z
      ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
    dsimp only [Function.comp_def] at h
    change fderiv ℝ (fun w => ζ (x - w)) z (unitVector j) = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
      ContinuousLinearMap.id_apply, map_neg, coordinateDerivative]
  have h := hfg.2.2 _ htest
  simp only [Measure.restrict_univ, hder, mul_neg, integral_neg, neg_inj] at h
  exact h

private noncomputable def c19_gradientRecoveryBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith only [h]

private theorem c19_ae_tendsto_recovered_weakDerivative {d : ℕ}
    {f g : Vec d → ℝ} {j : Fin d}
    (hfg : HasWeakPartialDerivative Set.univ j f g) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        coordinateDerivative j ((c19_gradientRecoveryBump d n).normed volume)) x)
        atTop (𝓝 (g x)) := by
  have hg : LocallyIntegrable g volume := locallyIntegrableOn_univ.mp hfg.2.1
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := c19_gradientRecoveryBump d)
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall fun n => (show
      1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2) by ring_nf; rfl)) hg
  filter_upwards [hconv] with x hx
  convert hx using 1
  funext n
  rw [c19_convolution_weak_partial hfg
    (c19_gradientRecoveryBump d n).contDiff_normed
    (c19_gradientRecoveryBump d n).hasCompactSupport_normed]
  rw [convolution_eq_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => mul_comm _ _

private noncomputable def c19_mollifiedGradientCoordinate {Ω : Type*} {d : ℕ}
    (f : Ω → Vec d → ℝ) (n : ℕ) (j : Fin d) (z : Ω × Vec d) : ℝ :=
  (f z.1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    coordinateDerivative j ((c19_gradientRecoveryBump d n).normed volume)) z.2

private theorem c19_measurable_mollifiedGradientCoordinate {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (f : Ω → Vec d → ℝ)
    (hfm : Measurable (fun z : Ω × Vec d => f z.1 z.2)) (n : ℕ) (j : Fin d) :
    Measurable (c19_mollifiedGradientCoordinate f n j) := by
  have hD : Continuous (coordinateDerivative j ((c19_gradientRecoveryBump d n).normed volume)) :=
    ((contDiff_infty_iff_fderiv.mp (c19_gradientRecoveryBump d n).contDiff_normed).2.clm_apply
      contDiff_const).continuous
  have hm : Measurable (fun z : (Ω × Vec d) × Vec d =>
      f z.1.1 z.2 * coordinateDerivative j ((c19_gradientRecoveryBump d n).normed volume)
        (z.1.2 - z.2)) :=
    (hfm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hD.measurable.comp ((measurable_snd.comp measurable_fst).sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A jointly measurable scalar field determines a measurable recovery of
all its actual whole-space weak gradients. No measurability of a chosen
gradient family is assumed. Source: `paper/main.tex:779–806,903–915`. -/
private theorem c19_exists_measurable_spatialGradient_recovery {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (f : Ω → Vec d → ℝ)
    (hfm : Measurable (fun z : Ω × Vec d => f z.1 z.2)) :
    ∃ H : Ω → Vec d → Vec d,
      Measurable (fun z : Ω × Vec d => H z.1 z.2) ∧
      ∀ (ω : Ω) (G : Vec d → Vec d), HasWeakGradient Set.univ (f ω) G →
        (fun x => H ω x) =ᵐ[volume] G := by
  let H : Ω → Vec d → Vec d := fun ω x j =>
    liminf (fun n => c19_mollifiedGradientCoordinate f n j (ω, x)) atTop
  refine ⟨H, ?_, ?_⟩
  · apply measurable_pi_lambda
    intro j
    exact Measurable.liminf (fun n => c19_measurable_mollifiedGradientCoordinate f hfm n j)
  · intro ω G hω
    have hconv (j : Fin d) : ∀ᵐ x ∂(volume : Measure (Vec d)),
        Tendsto (fun n => c19_mollifiedGradientCoordinate f n j (ω, x)) atTop (𝓝 (G x j)) := by
      change ∀ᵐ x ∂(volume : Measure (Vec d)),
        Tendsto (fun n => ((f ω) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          coordinateDerivative j ((c19_gradientRecoveryBump d n).normed volume)) x)
          atTop (𝓝 (G x j))
      exact c19_ae_tendsto_recovered_weakDerivative
        (f := f ω) (g := fun x => G x j) (j := j) (hω j)
    filter_upwards [ae_all_iff.mpr hconv] with x hx
    funext j
    exact (hx j).liminf_eq

/-- A jointly measurable complex potential determines a jointly measurable
version of every actual physical H1 gradient, including when the parameter
space carries the local coefficient sigma algebra. -/
theorem c19_measurable_physical_gradient_recovery
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (v : Ω → Lp ℂ 2 (volume : Measure (Vec d)))
    (V : Ω × Vec d → ℂ) (hV : Measurable V)
    (htrace : ∀ ω, (fun x => V (ω, x)) =ᵐ[volume] v ω) :
    ∃ H : Ω → Vec d → Fin d → ℂ,
      Measurable (fun p : Ω × Vec d => H p.1 p.2) ∧
      ∀ (ω : Ω) (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) (v ω) K →
          (fun x => H ω x) =ᵐ[volume] (fun x j => K j x) := by
  obtain ⟨R, hR, heR⟩ := c19_exists_measurable_spatialGradient_recovery
    (fun ω x => (V (ω, x)).re) (Complex.measurable_re.comp hV)
  obtain ⟨I, hI, heI⟩ := c19_exists_measurable_spatialGradient_recovery
    (fun ω x => (V (ω, x)).im) (Complex.measurable_im.comp hV)
  refine ⟨fun ω x j => (R ω x j : ℂ) + (I ω x j : ℂ) * Complex.I, ?_, ?_⟩
  · apply measurable_pi_lambda
    intro j
    exact (Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp hR)).add
      ((Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp hI)).mul measurable_const)
  · intro ω K hK
    have hrweak : HasWeakGradient univ (fun x => (V (ω, x)).re)
        (fun x j => (K j x).re) := by
      intro j
      apply (hK.1 j).congr_ae _ Filter.EventuallyEq.rfl
      rw [Measure.restrict_univ]
      filter_upwards [htrace ω] with x hx
      exact congrArg Complex.re hx.symm
    have hiweak : HasWeakGradient univ (fun x => (V (ω, x)).im)
        (fun x j => (K j x).im) := by
      intro j
      apply (hK.2 j).congr_ae _ Filter.EventuallyEq.rfl
      rw [Measure.restrict_univ]
      filter_upwards [htrace ω] with x hx
      exact congrArg Complex.im hx.symm
    filter_upwards [heR ω (fun x j => (K j x).re) hrweak,
      heI ω (fun x j => (K j x).im) hiweak] with x hr hi
    funext j
    rw [congrFun hr j, congrFun hi j]
    exact Complex.re_add_im (K j x)

/-- The Gaussian moment in primitive coercivity is absorbed by a Gaussian
with twice the spatial scale. -/
private theorem c19_gaussian_moment_le {q L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    (2 * q / (L * r ^ 2)) * Real.exp (-q / (L * r)) ^ 2 ≤
      (2 / r) * Real.exp (-q / (2 * L * r)) ^ 2 := by
  let z := q / (L * r)
  have he : z * Real.exp (-z) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one z).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hsq : Real.exp (-q / (2 * L * r)) ^ 2 = Real.exp (-z) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [z]
    push_cast
    field_simp [hL.ne', hr.ne']
    <;> ring
  calc
    _ = ((2 / r) * Real.exp (-z)) * (z * Real.exp (-z)) := by
      dsimp only [z]
      simp only [neg_div]
      field_simp [hL.ne', hr.ne']
      <;> ring
    _ ≤ ((2 / r) * Real.exp (-z)) * 1 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [hsq]; ring

/-- Recentring and averaging a jointly local spatial field preserves
locality on the Minkowski sum of its averaging and observation windows. -/
theorem c19_measurable_local_recentered_average {d : ℕ} {S U W : Set (Vec d)}
    (hS : MeasurableSet S) (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W)
    (k : Vec d → ℝ) (hk : Measurable k) (H : FieldPair d × Vec d → ℂ)
    (hH : @Measurable (FieldPair d × Vec d) ℂ
      (@Prod.instMeasurableSpace (FieldPair d) (Vec d) (localSigma U) inferInstance)
      inferInstance H) :
    Measurable[localSigma W]
      (fun ω => ∫ x in S, k x • H (translate x ω, -x)) := by
  classical
  let : MeasurableSpace (FieldPair d) := localSigma W
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x0, hx0⟩
  · subst S
    simpa only [setIntegral_empty] using
      (measurable_const : Measurable[localSigma W] (fun _ : FieldPair d => (0 : ℂ)))
  · let repair : Vec d → Vec d := fun x => if x ∈ S then x else x0
    have hmem : ∀ x, repair x ∈ S := by
      intro x
      dsimp only [repair]
      split_ifs with hx
      · exact hx
      · exact hx0
    let rep : Vec d → S := fun x => ⟨repair x, hmem x⟩
    have hrep : Measurable rep :=
      (Measurable.ite hS measurable_id measurable_const).subtype_mk
    have hrep_id : ∀ x ∈ S, (rep x : Vec d) = x := by
      intro x hx
      exact ite_eq_left hx
    have hpair : @Measurable (Vec d × FieldPair d) (S × FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W))
        (@Prod.instMeasurableSpace S (FieldPair d) _ (localSigma W))
        (fun q => (rep q.1, q.2)) :=
      (hrep.comp measurable_fst).prodMk measurable_snd
    have hT : @Measurable (Vec d × FieldPair d) (FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) (localSigma U)
        (fun q => translate (rep q.1 : Vec d) q.2) :=
      (measurable_translate_joint hSW).comp hpair
    have hk' : Measurable (fun q : Vec d × FieldPair d => S.indicator k q.1) :=
      (hk.indicator hS).comp measurable_fst
    have hF : Measurable (fun q : Vec d × FieldPair d =>
        S.indicator k q.1 • H (translate (rep q.1 : Vec d) q.2, -q.1)) :=
      hk'.smul (hH.comp (hT.prodMk measurable_fst.neg))
    have hfun : (fun ω : FieldPair d => ∫ x in S, k x • H (translate x ω, -x)) =
        fun ω : FieldPair d =>
          ∫ x, S.indicator k x • H (translate (rep x : Vec d) ω, -x) := by
      funext ω
      rw [← integral_indicator hS]
      congr 1
      funext x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx, hrep_id x hx]
      · simp only [Set.indicator_of_notMem hx, zero_smul]
    rw [hfun]
    exact (hF.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

/-- A strongly measurable L² family admits one jointly measurable spatial
representative agreeing with every member of the original family. -/
theorem c19_joint_l2_representative {T Ω : Type*}
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

/-- A measurable L2 potential family has a measurable spatial gradient
recovery agreeing with every physical H1 graph, without a measurable choice
of graph witnesses. -/
theorem c19_stronglyMeasurable_physical_gradient_recovery
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (v : Ω → Lp ℂ 2 (volume : Measure (Vec d))) (hv : StronglyMeasurable v) :
    ∃ H : Ω → Vec d → Fin d → ℂ,
      Measurable (fun p : Ω × Vec d => H p.1 p.2) ∧
      ∀ (ω : Ω) (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) (v ω) K →
          (fun x => H ω x) =ᵐ[volume] (fun x j => K j x) := by
  obtain ⟨V, hV, heV⟩ := c19_joint_l2_representative hv
  exact c19_measurable_physical_gradient_recovery v V hV heV


/-- Spatial averaging controls the squared error of a local recovered
representative by its joint spatial error. -/
theorem c19_finite_average_squared_error
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (ν : Measure T) [IsFiniteMeasure ν] (μ : Measure Ω) [SFinite μ]
    {J : T × Ω → ℂ} (hJ : Measurable J)
    (hI : Integrable (fun p => ‖J p‖ ^ 2) (ν.prod μ)) :
    Integrable (fun ω => ‖∫ x, J (x, ω) ∂ν‖ ^ 2) μ ∧
      (∫ ω, ‖∫ x, J (x, ω) ∂ν‖ ^ 2 ∂μ) ≤
        ν.real Set.univ * ∫ ω, ∫ x, ‖J (x, ω)‖ ^ 2 ∂ν ∂μ := by
  have hm : Measurable (fun ω => ∫ x, J (x, ω) ∂ν) :=
    (hJ.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable
  have hp : ∀ᵐ ω ∂μ, ‖∫ x, J (x, ω) ∂ν‖ ^ 2 ≤
      ν.real Set.univ * ∫ x, ‖J (x, ω)‖ ^ 2 ∂ν := by
    filter_upwards [hI.prod_left_ae] with ω hω
    exact c19_finite_integral_sq_bound
      ((memLp_two_iff_integrable_sq_norm
        (hJ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hω)
  have hi : Integrable (fun ω => ‖∫ x, J (x, ω) ∂ν‖ ^ 2) μ := by
    apply (hI.integral_prod_right.const_mul (ν.real Set.univ)).mono'
      (hm.norm.pow_const 2).aestronglyMeasurable
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, ν.real Set.univ * (∫ x, ‖J (x, ω)‖ ^ 2 ∂ν) ∂μ :=
      integral_mono_ae hi (hI.integral_prod_right.const_mul _) hp
    _ = _ := integral_const_mul _ _


/-- The actual transpose primitive has a global Euclidean H1 bound on the
first unit interval. Its constant depends only on the coefficient and force
bounds, so retained-data norm estimates can supply the spatial tail. -/
theorem c19_physical_transpose_primitive_H1_bound
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {B : ℝ} (hB : 0 ≤ B) (hζ : ‖ζ‖ ≤ B)
    {P T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hT : IsPhysicalComplexTransposeSemigroup a i ζ P T)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
    let M := Real.exp ((d : ℝ) * Λ ^ 3 * B ^ 2)
    let C := M ^ 2 + 4 * Λ * M * (M + 1) +
      4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * B ^ 2 * M ^ 2
    let v := ∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal f
    ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ‖v‖ ^ 2 + (∑ j, ‖K j‖ ^ 2) ≤ C * ‖f‖ ^ 2 := by
  intro M C v
  have hα : 0 ≤ (d : ℝ) * Λ ^ 3 * B ^ 2 := by positivity
  have hM : 0 < M := Real.exp_pos _
  have hM2 : M ^ 2 = Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2)) := by
    dsimp only [M]
    rw [← Real.exp_nat_mul] <;> norm_num
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖T s.toNNReal f‖ ≤ M * ‖f‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) *
          (s.toNNReal : ℝ)) * ‖f‖ ^ 2 :=
        short_time_physical_transpose_norm_sq_bound ha hΛ hA hζ hT f s.toNNReal
      _ ≤ Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2)) * ‖f‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply Real.exp_le_exp.mpr
        rw [Real.coe_toNNReal s hs.1]
        exact mul_le_of_le_one_right (by positivity) hs.2
      _ = _ := by rw [mul_pow, hM2]
  have hv : ‖v‖ ≤ M * ‖f‖ := by
    have hi : ‖v‖ ≤ (M * ‖f‖) * (t : ℝ) := by
      dsimp only [v]
      have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict
        (Icc (0 : ℝ) (t : ℝ))) (show ∀ᵐ s ∂volume.restrict
          (Icc (0 : ℝ) (t : ℝ)), ‖T s.toNNReal f‖ ≤ M * ‖f‖ from by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hb s ⟨hs.1, hs.2.trans ht⟩)
      simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        sub_zero, ENNReal.toReal_ofReal t.coe_nonneg] using hi
    exact hi.trans (mul_le_of_le_one_right (by positivity) ht)
  have htf : ‖T t f‖ ≤ M * ‖f‖ := by
    simpa only [Real.toNNReal_coe] using hb (t : ℝ) ⟨t.coe_nonneg, ht⟩
  have hres : ‖T t f - f‖ ≤ (M + 1) * ‖f‖ :=
    (norm_sub_le _ _).trans (by nlinarith only [htf])
  have hv2 : ‖v‖ ^ 2 ≤ M ^ 2 * ‖f‖ ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hv
  have hprod : ‖v‖ * ‖T t f - f‖ ≤ M * (M + 1) * ‖f‖ ^ 2 := by
    calc
      _ ≤ (M * ‖f‖) * ((M + 1) * ‖f‖) :=
        mul_le_mul hv hres (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hz2 : ‖ζ‖ ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (norm_nonneg _) hB).mpr hζ
  have hvg : IsPhysicalComplexTransposeGeneratorPair a i ζ v (T t f - f) := by
    have h := physical_transpose_generator_timeIntegral a i ζ P T hT f t
    have he : (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal f) =
        ∫ s in (0 : ℝ)..(t : ℝ), T s.toNNReal f :=
      integral_Icc_eq_integral_Ioc.trans
        (intervalIntegral.integral_of_le t.coe_nonneg).symm
    simpa only [v, he] using h
  obtain ⟨K, hK, hgrad⟩ := physical_complex_transpose_generator_gradient_bound
    a i ζ ha hΛ hA hvg
  refine ⟨K, hK, ?_⟩
  have hforce : ‖ζ‖ ^ 2 * ‖v‖ ^ 2 ≤ B ^ 2 * (M ^ 2 * ‖f‖ ^ 2) :=
    mul_le_mul hz2 hv2 (sq_nonneg _) (sq_nonneg _)
  have hgrad' : (∑ j, ‖K j‖ ^ 2) ≤
      4 * Λ * (M * (M + 1) * ‖f‖ ^ 2) +
        (4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4) * (B ^ 2 * (M ^ 2 * ‖f‖ ^ 2)) :=
    hgrad.trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * Λ by positivity),
        mul_le_mul_of_nonneg_left hforce
          (show 0 ≤ 4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 by positivity)])
  dsimp only [C]
  nlinarith only [hv2, hgrad']

/-- The actual retained transpose primitive supplies its own Gaussian forcing
bound. Agreement of the two coefficients on the interior ball places the
entire coefficient defect in the exterior. -/
theorem c19_transpose_primitive_exterior_forcing
    {d : ℕ} {A b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (hA : ∀ j k, MemLp (fun x => (A x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hAe : ∀ᵐ x ∂volume, S5Elliptic (A x) Λ)
    (hbe : ∀ᵐ x ∂volume, S5Elliptic (b x) Λ)
    {B : ℝ} (hB : 0 ≤ B) (hζ : ‖ζ‖ ≤ B)
    {P T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ P T)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) (ht : (t : ℝ) ≤ 1)
    {ρ σ : ℝ} (hσ : 0 < σ)
    (hinterior : ∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → b x = A x) :
    let M := Real.exp ((d : ℝ) * Λ ^ 3 * B ^ 2)
    let C := M ^ 2 + 4 * Λ * M * (M + 1) +
      4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * B ^ 2 * M ^ 2
    let N := 2 * (d : ℝ) * (2 * Λ) ^ 2 * d +
      2 * d * B ^ 2 * (2 * Λ) ^ 2
    let v := ∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal f
    ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      let R : Fin d → Vec d → ℂ := fun j x => (1 / 2 : ℂ) *
        (∑ k, ((A x j k - b x k j : ℝ) : ℂ) * K k x) -
        ζ * ((A x j i - b x j i : ℝ) : ℂ) * v x
      Integrable (fun x => Real.exp (-euclideanSq x / σ) ^ 2 * ∑ j, ‖R j x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / σ) ^ 2 * ∑ j, ‖R j x‖ ^ 2) ≤
        Real.exp (-2 * ρ ^ 2 / σ) * (N * C * ‖f‖ ^ 2) := by
  intro M C N v
  obtain ⟨K, hK, hnorm⟩ := c19_physical_transpose_primitive_H1_bound
    hb hΛ hbe hB hζ hT f t ht
  refine ⟨K, hK, ?_⟩
  intro R
  have hzero : ∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → ∀ j,
      (1 / 2 : ℂ) * (∑ k, ((A x j k - b x k j : ℝ) : ℂ) * K k x) -
        ζ * ((A x j i - b x j i : ℝ) : ℂ) * v x = 0 := by
    filter_upwards [hinterior, hAe] with x hx hAx hsmall j
    rw [hx hsmall]
    simp only [hAx.symm j, sub_self, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, mul_zero, sub_zero]
  obtain ⟨hi, htail⟩ := short_time_transpose_exterior_flux_energy
    hA hb hΛ hAe hbe hζ (show 0 < σ / 2 by positivity)
    (show (0 : ℝ) ≤ 0 by rfl) (show (0 : ℝ) ≤ 1 by norm_num) v K hzero
  have hw : (σ / 2) * (2 - (0 : ℝ)) = σ := by ring
  have he : -ρ ^ 2 / (σ / 2) = -2 * ρ ^ 2 / σ := by
    field_simp [hσ.ne'] <;> ring
  simp only [hw, he] at hi htail
  refine ⟨hi, htail.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))⟩
  have hg : 0 ≤ ∑ j, ‖K j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have ha0 : 0 ≤ 2 * (d : ℝ) * (2 * Λ) ^ 2 * d := by positivity
  have hb0 : 0 ≤ 2 * (d : ℝ) * B ^ 2 * (2 * Λ) ^ 2 := by positivity
  calc
    _ ≤ N * (‖v‖ ^ 2 + ∑ j, ‖K j‖ ^ 2) := by
      dsimp only [N]
      nlinarith only [mul_nonneg ha0 hv, mul_nonneg hb0 hg]
    _ ≤ N * (C * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (add_nonneg ha0 hb0)
    _ = _ := by ring

private theorem c19_gaussian_energy_mono {d : ℕ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (u : Vec d → ℂ) (hu : Measurable u)
    (hU : MemLp (fun x => (Real.exp (-euclideanSq x / R) : ℂ) * u x) 2 volume) :
    Integrable (fun x => Real.exp (-euclideanSq x / r) ^ 2 * ‖u x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / r) ^ 2 * ‖u x‖ ^ 2) ≤
        ∫ x, Real.exp (-euclideanSq x / R) ^ 2 * ‖u x‖ ^ 2 := by
  have hR : 0 < R := hr.trans_le hrR
  have hw (x : Vec d) : Real.exp (-euclideanSq x / r) ≤
      Real.exp (-euclideanSq x / R) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ hr hR).mpr
    nlinarith only [mul_nonneg (euclideanSq_nonneg_coords x) (sub_nonneg.mpr hrR)]
  have hm : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / r) : ℂ) * u x) := by
    have hg : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / r) : ℂ)) := by
      dsimp only [euclideanSq, dot]
      fun_prop
    exact hg.mul hu
  have hmem : MemLp (fun x => (Real.exp (-euclideanSq x / r) : ℂ) * u x) 2 volume := by
    apply hU.of_le hm.aestronglyMeasurable
    filter_upwards with x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hw x) (norm_nonneg _)
  have hi : Integrable (fun x => Real.exp (-euclideanSq x / r) ^ 2 * ‖u x‖ ^ 2) := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hmem.norm.integrable_sq
  have hI : Integrable (fun x => Real.exp (-euclideanSq x / R) ^ 2 * ‖u x‖ ^ 2) := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hU.norm.integrable_sq
  refine ⟨hi, integral_mono_ae hi hI ?_⟩
  filter_upwards with x
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_nonneg _) (hw x) 2) (sq_nonneg _)

/-- The actual transpose drift comparison controls a fixed Gaussian weight
with a right side independent of the short time. The retained datum remains
the same physical L2 datum throughout the estimate. -/
theorem c19_transpose_drift_fixed_gaussian_bound
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup b i ζ Pr Tr →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ ρ L : ℝ, 64 * Λ ^ 3 ≤ L →
        (∀ x, euclideanSq x < ρ ^ 2 → b x = ω.1 x) →
        (∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → (β i) (translate x ω) = fr x) →
      Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(Pdag t (β i)) (translate x ω) - (Tr t fr) x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(Pdag t (β i)) (translate x ω) - (Tr t fr) x‖ ^ 2) ≤
        Real.exp γ * (Real.exp (-ρ ^ 2 / (2 * L)) *
          (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr‖ ^ 2) +
          Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
            (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
              2 * d * B ^ 2 * (2 * Λ) ^ 2) *
            (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2)) * ‖fr‖ ^ 2)) := by
  intro Λ M γ t ht
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  filter_upwards [short_time_transpose_drift_gaussian_comparison hd D Q hQ β hβ i
    hP hPdag B hζ t ht,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (Pdag t (β i))] with ω hcomp hmem
  intro b hb hbe Pr Tr hTr fr ρ L hL hinterior hinitial
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  let Y : Vec d → ℂ := fun x => (Pdag t (β i)) (translate x ω) - (Tr t fr) x
  have hY : Measurable Y :=
    ((Lp.stronglyMeasurable _).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).sub (Lp.stronglyMeasurable _).measurable
  have hYwide : MemLp (fun x => (Real.exp (-euclideanSq x / (2 * L)) : ℂ) * Y x)
      2 volume := by
    simpa only [Y, mul_sub, Pi.sub_def] using
      (hmem (2 * L) (by positivity)).sub
        (c19_gaussian_weight_memLp (show 0 < 2 * L by positivity) (Tr t fr))
  have hwidth : L ≤ L * (2 - (t : ℝ)) := by
    nlinarith only [mul_le_mul_of_nonneg_left ht hLp.le]
  have hwide : L * (2 - (t : ℝ)) ≤ 2 * L := by
    nlinarith only [mul_nonneg hLp.le t.coe_nonneg]
  have hmoving : MemLp (fun x =>
      (Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) : ℂ) * Y x) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm (by
      have hw : Measurable (fun x : Vec d =>
          (Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) : ℂ)) := by
        dsimp only [euclideanSq, dot]
        fun_prop
      exact (hw.mul hY).aestronglyMeasurable)).mpr
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using
      (c19_gaussian_energy_mono (hLp.trans_le hwidth) hwide Y hY hYwide).1
  obtain ⟨hi, hmono⟩ := c19_gaussian_energy_mono hLp hwidth Y hY hmoving
  refine ⟨hi, hmono.trans ?_⟩
  have hc := hcomp b hb hbe Pr Tr hTr fr ρ L hL hinterior hinitial
  let N := 2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ)
  let H := 2 * (d : ℝ) * B ^ 2 * (2 * Λ) ^ 2
  let A := 2 * ((d : ℝ) * Λ ^ 3 * B ^ 2)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hNt : N + H * (t : ℝ) ≤ N + H := by
    linarith only [mul_le_mul_of_nonneg_left ht hH]
  have hEt : Real.exp (A * (t : ℝ)) ≤ Real.exp A :=
    Real.exp_le_exp.mpr (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ht hA)
  have htail := mul_le_mul hNt
    (mul_le_mul_of_nonneg_right hEt (sq_nonneg ‖fr‖))
    (mul_nonneg (Real.exp_nonneg _) (sq_nonneg ‖fr‖)) (add_nonneg hN hH)
  have hcoeff : 0 ≤ Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) := by positivity
  have htime := mul_le_mul_of_nonneg_left htail hcoeff
  have hgam : Real.exp (γ * (t : ℝ)) ≤ Real.exp γ :=
    Real.exp_le_exp.mpr (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ht hγ)
  have hR : 0 ≤ Real.exp (-ρ ^ 2 / (2 * L)) *
      (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr‖ ^ 2) +
      Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
        (N + H) * (Real.exp A * ‖fr‖ ^ 2) := by
    have hI : 0 ≤ ∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L)) :=
      integral_nonneg fun _ => Real.exp_nonneg _
    positivity
  have hupper := add_le_add
    (le_refl (Real.exp (-ρ ^ 2 / (2 * L)) *
      (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr‖ ^ 2))) htime
  simp only [mul_assoc] at hupper
  dsimp only [N, H, A] at hupper hR
  change Real.exp (-γ * (t : ℝ)) * (∫ x,
    Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 * ‖Y x‖ ^ 2) ≤ _ at hc
  simp only [mul_assoc] at hc hupper hR ⊢
  calc
    _ = Real.exp (γ * (t : ℝ)) *
        (Real.exp (-γ * (t : ℝ)) * ∫ x,
          Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 * ‖Y x‖ ^ 2) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [show γ * (t : ℝ) + -γ * (t : ℝ) = 0 by ring, Real.exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ ≤ _ := by
      simpa only [Λ, M, γ, mul_assoc] using
        mul_le_mul_of_nonneg_left hupper (Real.exp_nonneg (γ * (t : ℝ)))
    _ ≤ _ := mul_le_mul_of_nonneg_right hgam hR

/-- A measurable family of actual retained transpose evolutions inherits
the fixed Gaussian comparison after literal Bochner integration. The only
family assumptions identify the coefficients, initial data and semigroups;
the comparison and all temporal integrability are derived here. -/
theorem c19_transpose_measurable_primitive_gaussian_bound
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B)
    (b : FieldPair d → Vec d → Mat d)
    (fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    (V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)))
    (hfr : StronglyMeasurable fr) (hV : StronglyMeasurable (Function.uncurry V))
    (ρ L : ℝ)
    (hL : 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3 ≤ L)
    (hactual : ∀ᵐ ω ∂reducedLaw Q,
      (∀ j k, MemLp (fun x => (b ω x j k : ℂ)) ∞ volume) ∧
      (∀ᵐ x ∂volume, S5Elliptic (b ω x) (Real.exp (2 * D.ellipticity) * D.ellipticity)) ∧
      ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup (b ω) i ζ Pr Tr ∧
        ∀ s, V ω s = Tr s (fr ω))
    (hinterior : ∀ᵐ ω ∂reducedLaw Q,
      ∀ x, euclideanSq x < ρ ^ 2 → b ω x = ω.1 x)
    (hinitial : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂volume,
      euclideanSq x < ρ ^ 2 → (β i) (translate x ω) = fr ω x) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    let K : FieldPair d → ℝ := fun ω =>
      Real.exp γ * (Real.exp (-ρ ^ 2 / (2 * L)) *
        (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr ω‖ ^ 2) +
        Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
          (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
            2 * d * B ^ 2 * (2 * Λ) ^ 2) *
          (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2)) * ‖fr ω‖ ^ 2))
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
    let u := ∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal (β i)
    let v := fun ω => ∫ s in Icc (0 : ℝ) (t : ℝ), V ω s.toNNReal
    ∀ᵐ ω ∂reducedLaw Q,
      Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖u (translate x ω) - v ω x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖u (translate x ω) - v ω x‖ ^ 2) ≤ K ω := by
  intro Λ M γ K t ht u v
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let ν := volume.restrict (Icc (0 : ℝ) (t : ℝ))
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  have hfrnorm : Measurable (fun ω => ‖fr ω‖ ^ 2) := hfr.norm.measurable.pow_const 2
  have hKm : Measurable K := by dsimp only [K]; fun_prop
  have hK (ω : FieldPair d) : 0 ≤ K ω := by
    have hI : 0 ≤ ∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L)) :=
      integral_nonneg fun _ => Real.exp_nonneg _
    dsimp only [K]
    positivity
  obtain ⟨F, hF, heF⟩ := c19_joint_l2_representative
    (((hPdag.continuous_apply hP (β i)).comp continuous_real_toNNReal).stronglyMeasurable)
  obtain ⟨W, hW, heW⟩ := c19_joint_l2_representative
    (hV.comp_measurable (measurable_snd.prodMk
      (continuous_real_toNNReal.measurable.comp measurable_fst)))
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  have hw : Measurable w := by dsimp only [w, euclideanSq, dot]; fun_prop
  let E : (ℝ × FieldPair d) × Vec d → ℂ := fun p =>
    w p.2 * (F (p.1.1, translate p.2 p.1.2) - W p)
  have hE : Measurable E := (hw.comp measurable_snd).mul
    ((hF.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))).sub hW)
  have henergy : Measurable (fun p : ℝ × FieldPair d => ∫ x, ‖E (p, x)‖ ^ 2) :=
    (hE.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hpoint : ∀ᵐ s ∂ν, ∀ᵐ ω ∂reducedLaw Q,
      Integrable (fun x => ‖E ((s, ω), x)‖ ^ 2) ∧
        (∫ x, ‖E ((s, ω), x)‖ ^ 2) ≤ K ω := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hs1 : (s.toNNReal : ℝ) ≤ 1 := by
      rw [Real.coe_toNNReal _ hs.1]
      exact hs.2.trans ht
    filter_upwards [c19_transpose_drift_fixed_gaussian_bound hd D Q hQ β hβ i hP hPdag
        B hζ s.toNNReal hs1,
      hactual, hinterior, hinitial,
      ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
        (hF.comp (measurable_const.prodMk measurable_id))
        (Lp.stronglyMeasurable (Pdag s.toNNReal (β i))).measurable (heF s)]
      with ω hc ha hinter hinit hsp
    obtain ⟨hb, hbe, Pr, Tr, hTr, hVeq⟩ := ha
    obtain ⟨hi, hc⟩ := hc (b ω) hb hbe Pr Tr hTr (fr ω) ρ L hL hinter hinit
    have he : (fun x => ‖E ((s, ω), x)‖ ^ 2) =ᵐ[volume]
        (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
          ‖(Pdag s.toNNReal (β i)) (translate x ω) - (Tr s.toNNReal (fr ω)) x‖ ^ 2) := by
      filter_upwards [hsp, heW (s, ω)] with x hx hv
      dsimp only [Function.comp_apply, Function.uncurry, id_eq] at hx hv
      simp only [E, hx, hv, hVeq, norm_mul, mul_pow, w, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact ⟨hi.congr he.symm, (integral_congr_ae he).trans_le hc⟩
  have hgood : MeasurableSet {p : ℝ × FieldPair d |
      Integrable (fun x => ‖E (p, x)‖ ^ 2) ∧ (∫ x, ‖E (p, x)‖ ^ 2) ≤ K p.2} :=
    (measurableSet_integrable (hE.norm.pow_const 2).stronglyMeasurable).inter
      (measurableSet_le henergy (hKm.comp measurable_snd))
  have hpoint' := (Measure.ae_ae_comm hgood).mp hpoint
  have hfi := integrableOn_comp_toNNReal_Icc _ (hPdag.continuous_apply hP (β i)) (t : ℝ)
  have hIstat := integrable_sq_joint_l2_representative (ν := ν)
    ((((hPdag.continuous_apply hP (β i)).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hF heF
  filter_upwards [hpoint', hactual,
    ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF hIstat,
    ae_spatial_coeFn_integral_joint_l2_representative (reducedLaw Q)
      (reducedLaw_stationary Q) hfi hF heF] with ω hpointω ha htime htrace
  obtain ⟨_, _, Pr, Tr, hTr, hVeq⟩ := ha
  let Eω : ℝ × Vec d → ℂ := fun p => E ((p.1, ω), p.2)
  have hEω : Measurable Eω :=
    hE.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hIE : Integrable (fun p => ‖Eω p‖ ^ 2) (ν.prod volume) := by
    apply (integrable_prod_iff (hEω.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨hpointω.mono fun _ hs => hs.1, ?_⟩
    simp only [Real.norm_of_nonneg (sq_nonneg _)]
    apply (integrable_const (K ω)).mono'
      (hEω.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hpointω] with s hs
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact hs.2
  obtain ⟨hi, hb⟩ := c19_first_unit_spacetime_primitive_bound volume hEω t.coe_nonneg ht
    (hK ω) hIE (hpointω.mono fun _ hs => hs.2)
  have hvi : Integrable (fun s : ℝ => V ω s.toNNReal) ν := by
    change IntegrableOn (fun s : ℝ => V ω s.toNNReal) (Icc 0 (t : ℝ)) volume
    simpa only [hVeq] using
      integrableOn_comp_toNNReal_Icc _ (hTr.2.2.1 (fr ω)) (t : ℝ)
  have hWω : Measurable (fun p : ℝ × Vec d => W ((p.1, ω), p.2)) :=
    hW.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hvtrace := c19_integral_joint_l2_trace hvi hWω (fun s => heW (s, ω))
  have hsp : Measurable (fun p : ℝ × Vec d => F (p.1, translate p.2 ω)) :=
    hF.comp (measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const)))
  have he : (fun x => ‖(∫ s, Eω (s, x) ∂ν)‖ ^ 2) =ᵐ[volume]
      (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖u (translate x ω) - v ω x‖ ^ 2) := by
    filter_upwards [htrace, hvtrace, (htime L hLp).norm.integrable_sq.prod_left_ae]
      with x hx hv htx
    have hMF : MemLp (fun s => w x * F (s, translate x ω)) 2 ν :=
      (memLp_two_iff_integrable_sq_norm
        ((measurable_const.mul (hsp.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)).mpr htx
    have hFint : Integrable (fun s => F (s, translate x ω)) ν := by
      have hwi : w x ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
      apply ((hMF.integrable (by norm_num)).const_mul (w x)⁻¹).congr
      filter_upwards with s
      exact inv_mul_cancel_left₀ hwi _
    have hprimitive : (∫ s, Eω (s, x) ∂ν) = w x * (u (translate x ω) - v ω x) := by
      dsimp only [Eω, E]
      rw [integral_const_mul, integral_sub hFint hv.1, ← hx, ← hv.2]
    rw [hprimitive, norm_mul, mul_pow]
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨hi.congr he, ?_⟩
  rw [← integral_congr_ae he]
  exact hb

/-- The actual retained transpose evolution and its unit-time primitive have
one locally measurable gradient recovery. Every physical H1 graph of that
literal primitive is recovered, so no measurable choice of graphs is needed. -/
theorem c19_local_transpose_primitive_gradient_family {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcχ : HasCompactSupport χ) (U : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (i : Fin d) (ζ : ℂ) :
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ H : FieldPair d → Vec d → Fin d → ℂ,
      Measurable fr ∧ Measurable (Function.uncurry V) ∧
      Measurable (fun p : FieldPair d × Vec d => H p.1 p.2) ∧
      (∀ ω, IsSmoothFieldPair ω →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
          ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ)) ∧
      (∀ (ω : FieldPair d) (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl)
          (∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal) K →
          (fun x => H ω x) =ᵐ[volume] (fun x j => K j x)) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          IsPhysicalComplexTransposeSemigroup
            (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr ∧
          V ω 0 = fr ω ∧ Continuous (V ω) ∧
          ∀ t, V ω t = Tr t (fr ω) := by
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  obtain ⟨fr, V, hfr, hV, hefr, hactual⟩ :=
    short_time_transpose_cutoff_measurable_evolution χ hχ hcχ U hsupport Λ hΛ i ζ
  let v : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun ω => ∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal
  have hv : StronglyMeasurable v := by
    have hm : StronglyMeasurable (fun p : FieldPair d × ℝ => V p.1 p.2.toNNReal) :=
      hV.stronglyMeasurable.comp_measurable
        (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd))
    exact hm.integral_prod_right'
  obtain ⟨H, hH, heH⟩ := c19_stronglyMeasurable_physical_gradient_recovery v hv
  exact ⟨fr, V, H, hfr, hV, hH, hefr, heH, hactual⟩

/-- The physical retained-drift volume factor is absorbed by half of any
positive Gaussian rate, with constants chosen before the environment law. -/
theorem c19_retained_volume_gaussian_absorption (d : ℕ) {a : ℝ} (ha : 0 < a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (2 * ρ) ^ d * Real.exp (-a * ρ ^ 2) ≤
      (2 : ℝ) ^ d * Real.exp ((d : ℝ) ^ 2 / (2 * a)) *
        Real.exp (-(a / 2) * ρ ^ 2) := by
  have hp : ρ ^ d ≤ (Real.exp ρ) ^ d :=
    pow_le_pow_left₀ hρ
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ρ)) d
  have hs : (d : ℝ) * ρ - a / 2 * ρ ^ 2 ≤ (d : ℝ) ^ 2 / (2 * a) := by
    apply (le_div_iff₀ (show 0 < 2 * a by positivity)).mpr
    nlinarith only [sq_nonneg (a * ρ - (d : ℝ))]
  calc
    _ = (2 : ℝ) ^ d * (ρ ^ d * Real.exp (-a * ρ ^ 2)) := by
      rw [mul_pow]
      ring
    _ ≤ (2 : ℝ) ^ d * ((Real.exp ρ) ^ d * Real.exp (-a * ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)) (by positivity)
    _ = (2 : ℝ) ^ d * Real.exp ((d : ℝ) * ρ - a * ρ ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 2 <;> ring
    _ ≤ (2 : ℝ) ^ d * Real.exp ((d : ℝ) ^ 2 / (2 * a) - a / 2 * ρ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith only [hs])
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2 <;> ring

/-- The actual reduced drift and the complete retained transpose drift agree
on every open cutoff plateau, including its derivative contribution. -/
theorem c19_transpose_retained_drift_interior
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)) (U : Set (Vec d)), IsOpen U →
      (∀ x ∈ U, χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ∀ᵐ x ∂volume, x ∈ U → β i (translate x ω) = fr x := by
  filter_upwards [short_time_transpose_drift_spatial_identification hβ i] with ω hω
  intro χ U hU hχ fr hfr
  filter_upwards [hω, hfr] with x hx hfx
  intro hxU
  rw [hx, hfx, ForcedLocality.retainedPair_drift χ ω hU hχ hxU i]

private theorem c19_retained_elliptic {d : ℕ} (χ : C(Vec d, ℝ))
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

/-- Retention preserves the actual structural ellipticity and essential
coefficient bounds, on one event before the cutoff is selected. -/
theorem c19_retained_coefficients_admissible {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ))
        ∞ volume) ∧
      ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ := by
  intro Λ
  have hexp : 1 ≤ Real.exp (2 * Λ₀) :=
    Real.one_le_exp (by linarith [Q.ellipticity_parameter])
  have hΛ : 1 ≤ Λ :=
    one_le_mul_of_one_le_of_one_le hexp Q.ellipticity_parameter
  filter_upwards [c4_ae_reduced_physical_elliptic Q] with ω hA
  intro χ hχ
  have haret (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    c19_retained_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ hA x)
      (hχ x).1 (hχ x).2
  refine ⟨?_, haret⟩
  intro j k
  apply memLp_top_of_bound
    (Complex.continuous_ofReal.comp
      ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k)).aestronglyMeasurable Λ
  exact ae_of_all _ fun x => by
    change ‖((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)‖ ≤ Λ
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (haret x).entry_abs_le j k

/-- The generator-error pairing in Gaussian coercivity is controlled by the
two actual L2 errors. This also derives the pairing's integrability. -/
theorem c19_l2_pairing_lower_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * star (v x)) μ ∧
      -2 * (∫ x, u x * star (v x) ∂μ).re ≤
        (∫ x, ‖u x‖ ^ 2 ∂μ) + ∫ x, ‖v x‖ ^ 2 ∂μ := by
  have hi : Integrable (fun x => u x * star (v x)) μ := hu.integrable_mul hv.star
  have hui := hu.norm.integrable_sq
  have hvi := hv.norm.integrable_sq
  have hp (x : X) : -2 * (u x * star (v x)).re ≤ ‖u x‖ ^ 2 + ‖v x‖ ^ 2 := by
    have hr := Complex.abs_re_le_norm (u x * star (v x))
    simp only [norm_mul, norm_star] at hr
    nlinarith only [neg_abs_le (u x * star (v x)).re, hr,
      sq_nonneg (‖u x‖ - ‖v x‖)]
  have hb := integral_mono_ae (hi.re.const_mul (-2)) (hui.add hvi)
    (ae_of_all μ hp)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_re hi, integral_add hui hvi] at hb
  exact ⟨hi, hb⟩

/-- The actual retained transpose datum has a polynomial volume bound.
Absorbing that factor gives one structural Gaussian estimate for both the
literal time primitive and the terminal value of the same evolution. -/
theorem c19_transpose_retained_scalar_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (L : ℝ)
    (hL : 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3 ≤ L)
    (hLp : 0 < L) (Cχ : ℝ) (hCχ : 0 ≤ Cχ) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β →
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P Pdag →
      ‖ζ‖ ≤ 2 →
    ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ x, euclideanSq x < (ρ / 4) ^ 2 → χ x = 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ Cχ / ρ) →
    ∀ (fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
      (V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d))),
      StronglyMeasurable fr → StronglyMeasurable (Function.uncurry V) →
      (∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      (∀ᵐ ω ∂reducedLaw Q,
        ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexTransposeSemigroup
            (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr ∧
          ∀ s, V ω s = Tr s (fr ω)) →
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
    let u := ∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal (β i)
    let v := fun ω => ∫ s in Icc (0 : ℝ) (t : ℝ), V ω s.toNNReal
    ∀ᵐ ω ∂reducedLaw Q,
      (Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖u (translate x ω) - v ω x‖ ^ 2) ∧
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖u (translate x ω) - v ω x‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2)) ∧
      (Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(Pdag t (β i)) (translate x ω) - V ω t x‖ ^ 2) ∧
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖(Pdag t (β i)) (translate x ω) - V ω t x‖ ^ 2) ≤
            K * Real.exp (-c * ρ ^ 2)) := by
  let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
  let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
  let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * (2 : ℝ) ^ 2) + 1
  let T := (2 * (4 * Λ + 16 / L)) *
    (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) + 2 * d * (2 : ℝ) ^ 2 * (2 * Λ) ^ 2) *
      Real.exp (2 * ((d : ℝ) * Λ ^ 3 * (2 : ℝ) ^ 2))
  let A := (M + (1 / 2 : ℝ) * d * (Λ + 1) * Cχ) ^ 2
  let a := 1 / (32 * L)
  let E := (2 : ℝ) ^ d * Real.exp ((d : ℝ) ^ 2 / (2 * a))
  let D0 := 2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L)))
  let K := Real.exp γ * (D0 + (2 + |T|) * A * E + 1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hA : 0 ≤ A := sq_nonneg _
  have hD0 : 0 ≤ D0 := by
    have hI : 0 ≤ ∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L)) :=
      integral_nonneg fun _ => Real.exp_nonneg _
    dsimp only [D0]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨K, a / 2, ?_, by positivity, ?_⟩
  · dsimp only [K]
    positivity
  intro Q hQ β hβ i ζ P Pdag hP hPdag hζ χ hχ hχb ρ hρ hplateau hzero hder
    fr V hfr hV hefr heV t ht u v
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ]
    exact mul_nonneg (Real.exp_nonneg _) (zero_le_one.trans Q.ellipticity_parameter)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  let R : ℝ → ℝ := fun z => Real.exp γ *
    (Real.exp (-(ρ / 4) ^ 2 / (2 * L)) * (D0 + 2 * z) +
      Real.exp (-(ρ / 4) ^ 2 / L) * T * z)
  have habs (z : ℝ) (hz : 0 ≤ z) (hzbound : z ≤ A * (2 * ρ) ^ d) :
      R z ≤ K * Real.exp (-(a / 2) * ρ ^ 2) := by
    have heq : -(ρ / 4) ^ 2 / (2 * L) = -a * ρ ^ 2 := by
      dsimp only [a]
      field_simp [hLp.ne']
      <;> ring
    have htail : Real.exp (-(ρ / 4) ^ 2 / L) ≤ Real.exp (-a * ρ ^ 2) := by
      apply Real.exp_le_exp.mpr
      rw [← heq]
      apply (div_le_div_iff₀ hLp (show 0 < 2 * L by positivity)).mpr
      nlinarith only [mul_nonneg hLp.le (sq_nonneg (ρ / 4))]
    have hhalf : Real.exp (-a * ρ ^ 2) ≤ Real.exp (-(a / 2) * ρ ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg ha.le (sq_nonneg ρ)])
    have hza : Real.exp (-a * ρ ^ 2) * z ≤
        (A * E) * Real.exp (-(a / 2) * ρ ^ 2) := by
      calc
        _ ≤ Real.exp (-a * ρ ^ 2) * (A * (2 * ρ) ^ d) :=
          mul_le_mul_of_nonneg_left hzbound (Real.exp_nonneg _)
        _ = A * ((2 * ρ) ^ d * Real.exp (-a * ρ ^ 2)) := by ring
        _ ≤ A * (E * Real.exp (-(a / 2) * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (c19_retained_volume_gaussian_absorption d ha ρ (zero_le_one.trans hρ)) hA
        _ = _ := by ring
    calc
      R z ≤ Real.exp γ *
          (Real.exp (-a * ρ ^ 2) * D0 + (2 + T) * (Real.exp (-a * ρ ^ 2) * z)) := by
        dsimp only [R]
        rw [heq]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        nlinarith only [mul_le_mul_of_nonneg_right htail (mul_nonneg hT hz)]
      _ ≤ Real.exp γ *
          (Real.exp (-(a / 2) * ρ ^ 2) * D0 +
            (2 + T) * ((A * E) * Real.exp (-(a / 2) * ρ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact add_le_add (mul_le_mul_of_nonneg_right hhalf hD0)
          (mul_le_mul_of_nonneg_left hza (by positivity))
      _ ≤ K * Real.exp (-(a / 2) * ρ ^ 2) := by
        dsimp only [K]
        have hdiff := mul_nonneg
          (mul_nonneg (mul_nonneg (Real.exp_nonneg γ) (mul_nonneg hA hE))
            (Real.exp_nonneg (-(a / 2) * ρ ^ 2)))
          (sub_nonneg.mpr (le_abs_self T))
        nlinarith only [hdiff, mul_nonneg (Real.exp_nonneg γ)
          (Real.exp_nonneg (-(a / 2) * ρ ^ 2))]
  have hadm := c19_retained_coefficients_admissible Q
  have hactual : ∀ᵐ ω ∂reducedLaw Q,
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume) ∧
      (∀ᵐ x ∂volume, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) ∧
      ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr ∧
        ∀ s, V ω s = Tr s (fr ω) := by
    filter_upwards [hadm, heV] with ω hω hVω
    exact ⟨(hω χ hχb).1, ae_of_all _ (hω χ hχb).2, hVω⟩
  have hinterior : ∀ᵐ ω ∂reducedLaw Q,
      ∀ x, euclideanSq x < (ρ / 4) ^ 2 →
        (ForcedLocality.retainedPair χ ω).1 x = ω.1 x :=
    ae_of_all _ fun ω x hx => (ForcedLocality.retainedPair_eq_at χ ω (hplateau x hx)).1
  have hinitial : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂volume,
      euclideanSq x < (ρ / 4) ^ 2 → β i (translate x ω) = fr ω x := by
    filter_upwards [c19_transpose_retained_drift_interior hβ i, hefr] with ω hω hfrω
    exact hω χ {x | euclideanSq x < (ρ / 4) ^ 2}
      (isOpen_lt (by unfold euclideanSq dot; fun_prop) continuous_const)
      hplateau (fr ω) hfrω
  have hprimitive := c19_transpose_measurable_primitive_gaussian_bound hd D Q hQ β hβ i
    hP hPdag 2 hζ (fun ω => (ForcedLocality.retainedPair χ ω).1)
    fr V hfr hV (ρ / 4) L hL hactual hinterior hinitial t ht
  filter_upwards [hprimitive, hactual, hinterior, hinitial,
    c19_transpose_drift_fixed_gaussian_bound hd D Q hQ β hβ i hP hPdag 2 hζ t ht,
    short_time_transpose_actual_retained_drift_norm_sq hβ i, hefr] with
    ω hp hact hinter hinit hterminal hnorm hfrω
  obtain ⟨hb, hbe, Pr, Tr, hTr, hVeq⟩ := hact
  have hz : ‖fr ω‖ ^ 2 ≤ A * (2 * ρ) ^ d :=
    hnorm χ hχ Cχ ρ hCχ hρ hχb hzero hder (fr ω) hfrω
  have hp' : (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
      ‖u (translate x ω) - v ω x‖ ^ 2) ≤ R (‖fr ω‖ ^ 2) := by
    simpa only [R, D0, T, Λ, M, γ, mul_assoc] using hp.2
  obtain ⟨hti, htb⟩ := hterminal (ForcedLocality.retainedPair χ ω).1 hb hbe
    Pr Tr hTr (fr ω) (ρ / 4) L hL hinter hinit
  have ht' : (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
      ‖(Pdag t (β i)) (translate x ω) - V ω t x‖ ^ 2) ≤ R (‖fr ω‖ ^ 2) := by
    simpa only [hVeq, R, D0, T, Λ, M, γ, mul_assoc] using htb
  exact ⟨⟨hp.1, hp'.trans (habs _ (sq_nonneg _) hz)⟩,
    ⟨by simpa only [hVeq] using hti, ht'.trans (habs _ (sq_nonneg _) hz)⟩⟩

/-- The Gaussian pairing in primitive coercivity is bounded by the two
literal scalar errors, with no loss from narrowing the Gaussian. -/
theorem c19_gaussian_pairing_lower_bound {d : ℕ} {L : ℝ} (hL : 0 < L)
    (u q : Vec d → ℂ) (hu : Measurable u) (hq : Measurable q)
    (hU : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * u x) 2 volume)
    (hQ : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * q x) 2 volume) :
    Integrable (fun x => q x *
      (((Real.exp (-euclideanSq x / (L / 2)) ^ 2 : ℝ) : ℂ) * star (u x))) ∧
      -2 * (∫ x, q x *
        (((Real.exp (-euclideanSq x / (L / 2)) ^ 2 : ℝ) : ℂ) * star (u x))).re ≤
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2) +
          ∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖u x‖ ^ 2 := by
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / (L / 2)) : ℂ)
  have hw : Measurable w := by dsimp only [w, euclideanSq, dot]; fun_prop
  have hUm := c19_gaussian_energy_mono (show 0 < L / 2 by positivity)
    (show L / 2 ≤ L by linarith) u hu hU
  have hQm := c19_gaussian_energy_mono (show 0 < L / 2 by positivity)
    (show L / 2 ≤ L by linarith) q hq hQ
  have hnorm (z : Vec d → ℂ) (x : Vec d) :
      ‖w x * z x‖ ^ 2 = Real.exp (-euclideanSq x / (L / 2)) ^ 2 * ‖z x‖ ^ 2 := by
    simp only [w, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hUm' : MemLp (fun x => w x * u x) 2 volume :=
    (memLp_two_iff_integrable_sq_norm (hw.mul hu).aestronglyMeasurable).mpr
      (hUm.1.congr (ae_of_all _ fun x => (hnorm u x).symm))
  have hQm' : MemLp (fun x => w x * q x) 2 volume :=
    (memLp_two_iff_integrable_sq_norm (hw.mul hq).aestronglyMeasurable).mpr
      (hQm.1.congr (ae_of_all _ fun x => (hnorm q x).symm))
  obtain ⟨hi, hb⟩ := c19_l2_pairing_lower_bound hQm' hUm'
  have he : (fun x => (w x * q x) * star (w x * u x)) =
      (fun x => q x *
        (((Real.exp (-euclideanSq x / (L / 2)) ^ 2 : ℝ) : ℂ) * star (u x))) := by
    funext x
    simp only [w, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  rw [he] at hi hb
  simp only [hnorm] at hb
  exact ⟨hi, hb.trans (add_le_add hQm.2 hUm.2)⟩

/-- The negative derivative of the narrower Gaussian is controlled by the
wider scalar energy. Integrability is obtained from that same energy. -/
theorem c19_gaussian_primitive_moment_bound {d : ℕ} {L : ℝ} (hL : 0 < L)
    (u : Vec d → ℂ) (hu : Measurable u)
    (hU : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * u x) 2 volume) :
    Integrable (fun x => (-2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
      Real.exp (-euclideanSq x / (L * (1 / 2 : ℝ))) ^ 2) * ‖u x‖ ^ 2) ∧
      -(4 * ∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖u x‖ ^ 2) ≤
        ∫ x, (-2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
          Real.exp (-euclideanSq x / (L * (1 / 2 : ℝ))) ^ 2) * ‖u x‖ ^ 2 := by
  have hi : Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 * ‖u x‖ ^ 2) := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hU.norm.integrable_sq
  have hp (x : Vec d) :
      ‖(-2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
        Real.exp (-euclideanSq x / (L * (1 / 2 : ℝ))) ^ 2) * ‖u x‖ ^ 2‖ ≤
        4 * (Real.exp (-euclideanSq x / L) ^ 2 * ‖u x‖ ^ 2) := by
    have hmoment := c19_gaussian_moment_le (q := euclideanSq x) hL
      (show 0 < (1 / 2 : ℝ) by norm_num)
    have hw : 2 * L * (1 / 2 : ℝ) = L := by ring
    rw [hw] at hmoment
    norm_num only [div_self, show (2 : ℝ) / (1 / 2) = 4 by norm_num] at hmoment
    have hn : -2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (euclideanSq_nonneg_coords x))
        (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg _)) (sq_nonneg _))]
    have hprod := mul_le_mul_of_nonneg_right hmoment (sq_nonneg ‖u x‖)
    norm_num only at hprod ⊢
    convert hprod using 1 <;> ring
  have hm : AEStronglyMeasurable (fun x : Vec d =>
      (-2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
        Real.exp (-euclideanSq x / (L * (1 / 2 : ℝ))) ^ 2) * ‖u x‖ ^ 2) volume := by
    have hw : Measurable (fun x : Vec d =>
        -2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
          Real.exp (-euclideanSq x / (L * (1 / 2 : ℝ))) ^ 2) := by
      unfold euclideanSq dot
      fun_prop
    exact (hw.mul (hu.norm.pow_const 2)).aestronglyMeasurable
  have hmi := (hi.const_mul 4).mono' hm (ae_of_all _ hp)
  refine ⟨hmi, ?_⟩
  rw [← integral_const_mul, ← integral_neg]
  apply integral_mono_ae ((hi.const_mul 4).neg) hmi
  exact ae_of_all _ fun x => (neg_le_of_abs_le (hp x))

/-- The same actual forward retained evolution controls both its literal
time primitive and its terminal value, with one structural Gaussian width. -/
theorem c19_forward_clock_primitive_terminal_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ 2 →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
    let u := ∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → HasCompactSupport χ →
      (∀ x, euclideanNorm x ≤ ρ → χ x = 1) →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) →
    ∀ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr →
    let v := ∫ s in Icc (0 : ℝ) (t : ℝ), Pr s.toNNReal fr
    (Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖u (translate x ω) - v x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖u (translate x ω) - v x‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2)) ∧
    (Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) ≤
          K * Real.exp (-c * ρ ^ 2)) := by
  intro Λ
  obtain ⟨L, K, c, hscale, hL, hK, hc, hdec⟩ :=
    short_time_forward_clock_actual_gaussian_decay_common_event d hd D 2 (by norm_num)
  refine ⟨L, K, c, hscale, hL, hK, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f t ht u
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hgen : ∃ g, IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g := by
    cases ν with
    | inl j =>
      obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ j
      obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
        hQ ha ⟨0, by omega⟩ j
      exact ⟨b + ζ • c, hb.add (hc.smul ζ)⟩
    | inr z =>
      obtain ⟨c, hc⟩ := centeredEquations_clock_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
      exact ⟨ζ • c, hc.smul ζ⟩
  obtain ⟨g, hfg⟩ := hgen
  obtain ⟨F, U, hF, hU, heF, heU, hprimitive⟩ := short_time_stationary_joint_primitive hP hfg
  have hfi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)
  have hIstat := integrable_sq_joint_l2_representative
    (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := (t : ℝ)))) hF heF
  filter_upwards [hdec Q hQ β a μ hβ ha hμ ζ hζ P hP ν g F U hF hU heF heU hprimitive,
    short_time_stationary_primitive_gaussian_strong_continuous hd Q hP f g F U hU heU hprimitive,
    short_time_stationary_physical_gaussian_energy_continuous hd Q hP f g F U hU heU hprimitive,
    ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF hIstat,
    ae_spatial_coeFn_integral_joint_l2_representative (reducedLaw Q)
      (reducedLaw_stationary Q) hfi hF heF,
    ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (hF.comp (measurable_const.prodMk measurable_id))
      (Lp.stronglyMeasurable (P (t : ℝ).toNNReal f)).measurable (heF (t : ℝ))]
    with ω hdecω hmem hcont htime htrace hterminal
  intro χ ρ hρ hχ hcompact hin fr hfr Pr hPr v
  obtain ⟨V, hV, heV⟩ := short_time_physical_evolution_joint_representative hPr fr
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  let E : ℝ × Vec d → ℂ := fun p => w p.2 * (F (p.1, translate p.2 ω) - V p)
  have hw : Measurable w := by dsimp only [w, euclideanSq, dot]; fun_prop
  have hsp : Measurable (fun p : ℝ × Vec d => F (p.1, translate p.2 ω)) :=
    hF.comp (measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const)))
  have hE : Measurable E := (hw.comp measurable_snd).mul (hsp.sub hV)
  have hEm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      MemLp (fun x => E (s, x)) 2 volume := by
    have hmV := (c19_gaussian_weight_memLp hL (Pr s.toNNReal fr)).ae_eq
      ((heV s).symm.mono fun x hx => congrArg (fun z : ℂ => w x * z) hx)
    simpa only [E, w, mul_sub, Pi.sub_def] using ((hmem L hL).1 s hs).sub hmV
  have henergy (s : ℝ) : (∫ x, ‖E (s, x)‖ ^ 2) =
      ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (s, translate x ω) - V (s, x)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [E, w, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hIE : Integrable (fun p => ‖E p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod volume) := by
    apply (integrable_prod_iff (hE.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact (hEm s ⟨hs.1, hs.2.trans ht⟩).norm.integrable_sq
    · have hi : IntegrableOn (fun s : ℝ => ∫ x,
          Real.exp (-euclideanSq x / L) ^ 2 *
            ‖F (s, translate x ω) - V (s, x)‖ ^ 2)
          (Icc (0 : ℝ) (t : ℝ)) :=
        ((hcont L hL (ForcedLocality.retainedPair χ ω).1 Pr hPr fr V heV).mono
          (Icc_subset_Icc le_rfl ht)).integrableOn_compact isCompact_Icc
      apply hi.congr
      filter_upwards with s
      simp only [Real.norm_of_nonneg (sq_nonneg _), henergy]
  have hbound : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      (∫ x, ‖E (s, x)‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [henergy]
    exact hdecω χ ρ hρ hχ hcompact hin fr hfr Pr hPr V heV s ⟨hs.1, hs.2.trans ht⟩
  obtain ⟨hi, hb⟩ := c19_first_unit_spacetime_primitive_bound volume hE
    t.coe_nonneg ht (by positivity) hIE hbound
  have hVtrace := c19_integral_joint_l2_trace
    (integrableOn_comp_toNNReal_Icc _ (hPr.2.2.1 fr) (t : ℝ)) hV heV
  have heq : (fun x => ‖∫ s in Icc (0 : ℝ) (t : ℝ), E (s, x)‖ ^ 2) =ᵐ[volume]
      (fun x => Real.exp (-euclideanSq x / L) ^ 2 * ‖u (translate x ω) - v x‖ ^ 2) := by
    filter_upwards [htrace, hVtrace, (htime L hL).norm.integrable_sq.prod_left_ae]
      with x hx hv htx
    have hMF : MemLp (fun s => w x * F (s, translate x ω)) 2
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) :=
      (memLp_two_iff_integrable_sq_norm
        ((measurable_const.mul (hsp.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)).mpr htx
    have hFint : IntegrableOn (fun s => F (s, translate x ω)) (Icc (0 : ℝ) (t : ℝ)) := by
      have hwi : w x ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
      apply ((hMF.integrable (by norm_num)).const_mul (w x)⁻¹).congr
      filter_upwards with s
      exact inv_mul_cancel_left₀ hwi _
    have he : (∫ s in Icc (0 : ℝ) (t : ℝ), E (s, x)) =
        w x * (u (translate x ω) - v x) := by
      dsimp only [E]
      rw [integral_const_mul, integral_sub hFint hv.1, ← hx, ← hv.2]
    rw [he, norm_mul, mul_pow]
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  constructor
  · refine ⟨hi.congr heq, ?_⟩
    rw [← integral_congr_ae heq]
    exact hb
  have het : (fun x => ‖E ((t : ℝ), x)‖ ^ 2) =ᵐ[volume]
      (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) := by
    filter_upwards [hterminal, heV (t : ℝ)] with x hx hv
    dsimp only [Function.comp_apply, id_eq] at hx hv
    simp only [Real.toNNReal_coe] at hx hv
    simp only [E, hx, hv, norm_mul, mul_pow, w, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨((hEm (t : ℝ) ⟨t.coe_nonneg, ht⟩).norm.integrable_sq).congr het, ?_⟩
  rw [← integral_congr_ae het, henergy]
  exact hdecω χ ρ hρ hχ hcompact hin fr hfr Pr hPr V heV (t : ℝ) ⟨t.coe_nonneg, ht⟩

/-- The actual retained transpose primitive has a Gaussian forcing tail.
The retained drift's volume growth is absorbed before choosing the law. -/
theorem c19_transpose_primitive_forcing_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (L : ℝ)
    (hLp : 0 < L) (Cχ : ℝ) (hCχ : 0 ≤ Cχ) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 2 →
    ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ x, euclideanSq x < (ρ / 4) ^ 2 → χ x = 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ Cχ / ρ) →
    ∀ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
    ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeSemigroup
        (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
    let v := ∫ s in Icc (0 : ℝ) (t : ℝ), Tr s.toNNReal (fr ω)
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) v H ∧
      let R : Fin d → Vec d → ℂ := fun j x => (1 / 2 : ℂ) *
        (∑ k, ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x k j : ℝ) : ℂ) * H k x) -
        ζ * ((ω.1 x j i -
          (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ) * v x
      Integrable (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ∑ j, ‖R j x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 * ∑ j, ‖R j x‖ ^ 2) ≤
        K * Real.exp (-c * ρ ^ 2) := by
  let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
  let M := Real.exp ((d : ℝ) * Λ ^ 3 * (2 : ℝ) ^ 2)
  let C := M ^ 2 + 4 * Λ * M * (M + 1) +
    4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * (2 : ℝ) ^ 2 * M ^ 2
  let N := 2 * (d : ℝ) * (2 * Λ) ^ 2 * d +
    2 * d * (2 : ℝ) ^ 2 * (2 * Λ) ^ 2
  let A := ((1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity +
    (1 / 2 : ℝ) * d * (Λ + 1) * Cχ) ^ 2
  let a := 1 / (4 * L)
  let E := (2 : ℝ) ^ d * Real.exp ((d : ℝ) ^ 2 / (2 * a))
  let K := |N * C| * A * E + 1
  have ha : 0 < a := by dsimp only [a]; positivity
  have hA : 0 ≤ A := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨K, a / 2, ?_, by positivity, ?_⟩
  · dsimp only [K]; positivity
  intro Q hQ β hβ i ζ hζ χ hχ hχb ρ hρ hplateau hzero hder fr hefr t ht
  have hΛ1 : 1 ≤ Λ := by
    dsimp only [Λ]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp (by linarith [Q.ellipticity_parameter])) Q.ellipticity_parameter
  have hΛ : 0 < Λ := zero_lt_one.trans_le hΛ1
  have hNC : 0 ≤ N * C := by dsimp only [N, C, M]; positivity
  filter_upwards [c4_ae_reduced_physical_elliptic Q,
    c19_retained_coefficients_admissible Q,
    short_time_transpose_actual_retained_drift_norm_sq hβ i, hefr]
    with ω hω hret hnorm hfr
  intro Pr Tr hTr v
  have hAe : ∀ x, S5Elliptic (ω.1 x) Λ := s5Elliptic_of_isElliptic hΛ1 hω
  have hAentry (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hω
      (fun j k => ω.1.continuous.matrix_elem j k) j k
  have hinterior : ∀ᵐ x ∂volume, euclideanSq x < (ρ / 4) ^ 2 →
      (ForcedLocality.retainedPair χ ω).1 x = ω.1 x :=
    ae_of_all _ fun x hx => (ForcedLocality.retainedPair_eq_at χ ω (hplateau x hx)).1
  obtain ⟨H, hH, hi, hb⟩ := c19_transpose_primitive_exterior_forcing
    hAentry (hret χ hχb).1 hΛ (ae_of_all _ hAe) (ae_of_all _ (hret χ hχb).2)
    (show (0 : ℝ) ≤ 2 by norm_num) hζ hTr (fr ω) t ht
    (show 0 < L / 2 by positivity) hinterior
  refine ⟨H, hH, hi, hb.trans ?_⟩
  have hfrnorm : ‖fr ω‖ ^ 2 ≤ A * (2 * ρ) ^ d :=
    hnorm χ hχ Cχ ρ hCχ hρ hχb hzero hder (fr ω) hfr
  have hexponent : -2 * (ρ / 4) ^ 2 / (L / 2) = -a * ρ ^ 2 := by
    dsimp only [a]
    field_simp [hLp.ne'] <;> ring
  change Real.exp (-2 * (ρ / 4) ^ 2 / (L / 2)) * (N * C * ‖fr ω‖ ^ 2) ≤ _
  rw [hexponent]
  calc
    _ ≤ Real.exp (-a * ρ ^ 2) * (N * C * (A * (2 * ρ) ^ d)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfrnorm hNC) (Real.exp_nonneg _)
    _ = (N * C * A) * ((2 * ρ) ^ d * Real.exp (-a * ρ ^ 2)) := by ring
    _ ≤ (N * C * A) * (E * Real.exp (-(a / 2) * ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (c19_retained_volume_gaussian_absorption d ha ρ (zero_le_one.trans hρ))
        (mul_nonneg hNC hA)
    _ ≤ K * Real.exp (-(a / 2) * ρ ^ 2) := by
      dsimp only [K]
      have hh := mul_nonneg
        (mul_nonneg hA hE) (sub_nonneg.mpr (le_abs_self (N * C)))
      nlinarith only [mul_nonneg hh (Real.exp_nonneg (-(a / 2) * ρ ^ 2)),
        Real.exp_nonneg (-(a / 2) * ρ ^ 2)]

private theorem c19_unit_interval_integral_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ s in (0 : ℝ)..1, f s) = ∫ s in Icc (0 : ℝ) 1, f s :=
  (intervalIntegral.integral_of_le zero_le_one).trans integral_Icc_eq_integral_Ioc.symm

/-- Gaussian decay for the actual transpose primitive gradient, with the
same supplied finite-time flux and every physical gradient of the retained
primitive. All scalar comparisons are produced internally. -/
theorem c19_transpose_integrated_gradient_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (L : ℝ)
    (hL : 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3 ≤ L)
    (hLp : 0 < L) (Cχ : ℝ) (hCχ : 0 ≤ Cχ) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ‖ζ‖ ≤ 2 →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ x, euclideanSq x < (ρ / 4) ^ 2 → χ x = 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ Cχ / ρ) →
    ∀ (fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
      (V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d))),
      StronglyMeasurable fr → StronglyMeasurable (Function.uncurry V) →
      (∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j ⟨0, by omega⟩) x : ℝ) : ℂ)) →
      (∀ᵐ ω ∂reducedLaw Q,
        ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexTransposeSemigroup
            (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr Tr ∧
          ∀ s, V ω s = Tr s (fr ω)) →
    let H := fun j => ∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inr ()) j
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ J : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl)
        (∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal) J →
      Integrable (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ∑ j, ‖H j (translate x ω) - J j x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ∑ j, ‖H j (translate x ω) - J j x‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨Ks, cs, hKs, hcs, hscalar⟩ :=
    c19_transpose_retained_scalar_gaussian_decay d hd D L hL hLp Cχ hCχ
  obtain ⟨Kf, cf, hKf, hcf, hforcing⟩ :=
    c19_transpose_primitive_forcing_gaussian_decay d hd D L hLp Cχ hCχ
  let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
  let B := (4 * Λ + 16 / L) * (2 * d * Λ ^ 2 * (2 : ℝ) ^ 2)
  let C := 4 * Λ * ((B + 9) * Ks + (2 * (4 * Λ + 16 / L)) * Kf)
  let c := min cs cf
  refine ⟨|C| + 1, c, by positivity, lt_min hcs hcf, ?_⟩
  intro Q hQ β a μ hβ ζ P Pdag hP hPdag hζ G F hF χ hχ hχb ρ hρ
    hplateau hzero hder fr V hfr hV hefr heV H
  let i : Fin d := ⟨0, by omega⟩
  let f := β i
  let u := ∫ s in Icc (0 : ℝ) 1, Pdag s.toNNReal f
  let v := fun ω => ∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (zero_lt_one.trans_le Q.ellipticity_parameter)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsc := hscalar Q hQ β hβ i ζ P Pdag hP hPdag hζ χ hχ hχb ρ hρ
    hplateau hzero hder fr V hfr hV hefr heV
  have hfc := hforcing Q hQ β hβ i ζ hζ χ hχ hχb ρ hρ hplateau hzero hder fr hefr
    1 (by norm_num)
  have hcoerc := c19_transpose_integrated_gradient_gaussian_coercivity
    hd Q ζ P Pdag β a μ hP hPdag G F hF 1
  simp only [NNReal.coe_one, c19_unit_interval_integral_eq] at hcoerc
  have hsub := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (Pdag 1 f - f)).measurable
    ((Lp.stronglyMeasurable (Pdag 1 f)).measurable.sub (Lp.stronglyMeasurable f).measurable)
    (Lp.coeFn_sub (Pdag 1 f) f)
  filter_upwards [hsc 1 (by norm_num), hsc 0 (by norm_num), hfc, hcoerc, heV, hsub,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) u,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (Pdag 1 f - f)]
    with ω hs1 hs0 hfω hcω hact hsubω hmu hmq
  obtain ⟨Pr, Tr, hTr, hVeq⟩ := hact
  have hv (s : ℝ) : Tr s.toNNReal (fr ω) = V ω s.toNNReal := (hVeq _).symm
  have hv1 : Tr 1 (fr ω) = V ω 1 := (hVeq _).symm
  have hv0 : V ω 0 = fr ω := by rw [hVeq, hTr.1]; rfl
  have hsinitial : Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖f (translate x ω) - fr ω x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖f (translate x ω) - fr ω x‖ ^ 2) ≤ Ks * Real.exp (-cs * ρ ^ 2) := by
    simpa only [f, i, hPdag.zero hP, ContinuousLinearMap.id_apply, hv0] using hs0.2
  obtain ⟨J0, hJ0, hcoercive⟩ := hcω χ hχb Pr Tr hTr (fr ω)
  obtain ⟨J1, hJ1, hfi, hfb⟩ := hfω Pr Tr hTr
  simp only [hv] at hJ0 hcoercive hJ1 hfi hfb
  intro J hJ
  have he0 : J0 = J := physicalH1Graph_gradient_unique volume (Or.inl rfl) (v ω) J0 J hJ0 hJ
  have he1 : J1 = J := physicalH1Graph_gradient_unique volume (Or.inl rfl) (v ω) J1 J hJ1 hJ
  rw [he0] at hcoercive
  rw [he1] at hfi hfb
  let e : Vec d → ℂ := fun x => u (translate x ω) - v ω x
  let q : Vec d → ℂ := fun x => (Pdag 1 f - f) (translate x ω) - (Tr 1 (fr ω) - fr ω) x
  have horbit : Measurable (fun x : Vec d => translate x ω) :=
    Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)
  have he : Measurable e :=
    ((Lp.stronglyMeasurable u).measurable.comp horbit).sub (Lp.stronglyMeasurable (v ω)).measurable
  have hq : Measurable q :=
    ((Lp.stronglyMeasurable (Pdag 1 f - f)).measurable.comp horbit).sub
      (Lp.stronglyMeasurable (Tr 1 (fr ω) - fr ω)).measurable
  have hmU : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * e x) 2 volume := by
    simpa only [e, mul_sub, Pi.sub_def] using (hmu L hLp).sub
      (c19_gaussian_weight_memLp hLp (v ω))
  have hmQ : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * q x) 2 volume := by
    simpa only [q, mul_sub, Pi.sub_def] using (hmq L hLp).sub
      (c19_gaussian_weight_memLp hLp (Tr 1 (fr ω) - fr ω))
  have hqi : Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2) := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hmQ.norm.integrable_sq
  have hpoint : ∀ᵐ x ∂volume, Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2 ≤
      2 * (Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(Pdag 1 f) (translate x ω) - V ω 1 x‖ ^ 2) +
      2 * (Real.exp (-euclideanSq x / L) ^ 2 *
        ‖f (translate x ω) - fr ω x‖ ^ 2) := by
    filter_upwards [hsubω, Lp.coeFn_sub (Tr 1 (fr ω)) (fr ω)] with x hx hy
    have hqeq : q x = ((Pdag 1 f) (translate x ω) - V ω 1 x) -
        (f (translate x ω) - fr ω x) := by
      dsimp only [q]
      rw [hx, hy]
      simp only [Pi.sub_apply, hv1]
      ring
    rw [hqeq]
    have hn := norm_sub_le ((Pdag 1 f) (translate x ω) - V ω 1 x)
      (f (translate x ω) - fr ω x)
    have hn2 : ‖((Pdag 1 f) (translate x ω) - V ω 1 x) -
        (f (translate x ω) - fr ω x)‖ ^ 2 ≤
        2 * ‖(Pdag 1 f) (translate x ω) - V ω 1 x‖ ^ 2 +
          2 * ‖f (translate x ω) - fr ω x‖ ^ 2 := by
      nlinarith only [hn, norm_nonneg (((Pdag 1 f) (translate x ω) - V ω 1 x) -
        (f (translate x ω) - fr ω x)),
        sq_nonneg (‖(Pdag 1 f) (translate x ω) - V ω 1 x‖ - ‖f (translate x ω) - fr ω x‖)]
    nlinarith only [mul_le_mul_of_nonneg_left hn2 (sq_nonneg
      (Real.exp (-euclideanSq x / L)))]
  have hqbound := integral_mono_ae hqi ((hs1.2.1.const_mul 2).add (hsinitial.1.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hqbound
  rw [integral_add (hs1.2.1.const_mul 2) (hsinitial.1.const_mul 2),
    integral_const_mul, integral_const_mul] at hqbound
  have hqbound' : (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2) ≤
      4 * Ks * Real.exp (-cs * ρ ^ 2) := by
    nlinarith only [hqbound, hs1.2.2, hsinitial.2]
  obtain ⟨hpairi, hpair⟩ := c19_gaussian_pairing_lower_bound hLp e q he hq hmU hmQ
  obtain ⟨hmomi, hmom⟩ := c19_gaussian_primitive_moment_bound hLp e he hmU
  have hscalarwide : (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖e x‖ ^ 2) ≤
      Ks * Real.exp (-cs * ρ ^ 2) := hs1.1.2
  have hscalarnarrow := (c19_gaussian_energy_mono (show 0 < L / 2 by positivity)
    (show L / 2 ≤ L by linarith) e he hmU).2.trans hscalarwide
  have hcsrate : Real.exp (-cs * ρ ^ 2) ≤ Real.exp (-c * ρ ^ 2) :=
    Real.exp_le_exp.mpr (by
      simpa only [c, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left cs cf) (sq_nonneg ρ)))
  have hcfrate : Real.exp (-cf * ρ ^ 2) ≤ Real.exp (-c * ρ ^ 2) :=
    Real.exp_le_exp.mpr (by
      simpa only [c, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right cs cf) (sq_nonneg ρ)))
  have hscalarcommon := hscalarwide.trans (mul_le_mul_of_nonneg_left hcsrate hKs.le)
  have hqcommon := hqbound'.trans (mul_le_mul_of_nonneg_left hcsrate (by positivity : 0 ≤ 4 * Ks))
  have hforcecommon := hfb.trans (mul_le_mul_of_nonneg_left hcfrate hKf.le)
  have hζsq : ‖ζ‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith only [hζ, norm_nonneg ζ]
  have hcoef : (4 * Λ + 16 / L) * (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) ≤ B := by
    dsimp only [B]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hζsq (by positivity)) (by positivity)
  have hmain := mul_le_mul hcoef
    (hscalarnarrow.trans (mul_le_mul_of_nonneg_left hcsrate hKs.le))
    (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hB
  obtain ⟨hJi, hWi, hcineq⟩ := hcoercive L (1 / 2) hL (by norm_num)
  have hw : L * (1 / 2 : ℝ) = L / 2 := by ring
  simp only [hw] at hcineq hJi
  have hJbound : (Λ⁻¹ / 4) * (∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
      ∑ j, ‖H j (translate x ω) - J j x‖ ^ 2) ≤
      ((B + 9) * Ks + 2 * (4 * Λ + 16 / L) * Kf) * Real.exp (-c * ρ ^ 2) := by
    have hforce := mul_le_mul_of_nonneg_left hforcecommon
      (show 0 ≤ 2 * (4 * Λ + 16 / L) by positivity)
    change 2 * (∫ x, q x *
        (((Real.exp (-euclideanSq x / (L / 2)) ^ 2 : ℝ) : ℂ) * star (e x))).re +
      (∫ x, (-2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
        Real.exp (-euclideanSq x / (L / 2)) ^ 2) * ‖e x‖ ^ 2) + _ ≤ _ at hcineq
    rw [hw] at hmom
    simp only [NNReal.coe_one] at hforce
    dsimp only [Λ, H, e, u, v, f, i] at hcineq hforce hmain hpair hmom hscalarcommon hqcommon ⊢
    nlinarith only [hcineq, hforce, hmain, hpair, hmom, hscalarcommon, hqcommon]
  have hmult := mul_le_mul_of_nonneg_left hJbound (show 0 ≤ 4 * Λ by positivity)
  have hinv : (4 * Λ) * (Λ⁻¹ / 4) = 1 := by field_simp [hΛ.ne']
  simp only [← mul_assoc, hinv, one_mul] at hmult
  refine ⟨hJi, hmult.trans ?_⟩
  change C * Real.exp (-c * ρ ^ 2) ≤ (|C| + 1) * Real.exp (-c * ρ ^ 2)
  exact mul_le_mul_of_nonneg_right (by linarith only [le_abs_self C]) (Real.exp_nonneg _)

/-- The actual forward forcing estimate at the narrower coercivity weight.
The radius is the retained cutoff scale, and the constants precede the law. -/
theorem c19_forward_primitive_forcing_gaussian_decay
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (L : ℝ) (hL : 0 < L) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 2 →
    ∀ (ν : FluxIndex d) (t : ℝ≥0), (t : ℝ) ≤ 1 →
    let H := fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν j
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (χ : C(Vec d, ℝ)) (ρ : ℝ), 0 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanNorm x < ρ / 4 → χ x = 1) →
    let A := fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
      ∑ j : Fin d, ‖C9ShortTimeLocality.retainedFluxDefect χ ω x
        (fun k => H k (translate x ω)) j‖ ^ 2
    let B := fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
      ‖C9ShortTimeLocality.retainedDriftDefect χ ω x
        (fun k => H k (translate x ω)) ⟨0, by omega⟩ ζ‖ ^ 2
    Integrable A ∧ Integrable B ∧
      (∫ x, A x) + (∫ x, B x) ≤ K * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨C, hC, hforcing⟩ := c19_first_unit_integrated_gradient_retained_forcing hlocal d hd D
  let I := ∫ x : Vec d, Real.exp (-((4 / L) / 2) * euclideanSq x)
  have hI : 0 ≤ I := integral_nonneg fun _ => Real.exp_nonneg _
  refine ⟨C * I + 1, 1 / (8 * L), by positivity, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hF hζ ν t ht H
  filter_upwards [hforcing Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hF hζ ν t ht]
    with ω hω
  intro χ ρ hρ hχ hplateau A B
  obtain ⟨hi, hb⟩ := hω χ (4 / L) (ρ / 4) (by positivity) (by positivity) hχ hplateau
  have hw (x : Vec d) : Real.exp (-(4 / L) * euclideanSq x) =
      Real.exp (-euclideanSq x / (L / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hL.ne'] <;> ring
  simp only [hw, ← Finset.mul_sum] at hi hb
  change Integrable (fun x => A x + B x) at hi
  change (∫ x, A x + B x) ≤ _ at hb
  have hH (j : Fin d) : Measurable (fun x => H j (translate x ω)) :=
    (Lp.stronglyMeasurable (H j)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hωentry (j k : Fin d) : Continuous (fun x => ω.1 x j k) :=
    ω.1.continuous.matrix_elem j k
  have hretentry (j k : Fin d) : Continuous
      (fun x => (ForcedLocality.retainedPair χ ω).1 x j k) :=
    (ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k
  have hAm : AEStronglyMeasurable A volume := by
    apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    dsimp only [A, C9ShortTimeLocality.retainedFluxDefect, euclideanSq, dot]
    fun_prop
  have hBm : AEStronglyMeasurable B volume := by
    apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    dsimp only [B, C9ShortTimeLocality.retainedDriftDefect, euclideanSq, dot]
    fun_prop
  have hA0 (x : Vec d) : 0 ≤ A x :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB0 (x : Vec d) : 0 ≤ B x := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hAi : Integrable A := hi.mono' hAm (ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (hA0 x)]; exact le_add_of_nonneg_right (hB0 x))
  have hBi : Integrable B := hi.mono' hBm (ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (hB0 x)]; exact le_add_of_nonneg_left (hA0 x))
  refine ⟨hAi, hBi, ?_⟩
  rw [integral_add hAi hBi] at hb
  have he : -((4 / L) / 2) * (ρ / 4) ^ 2 = -(1 / (8 * L)) * ρ ^ 2 := by
    field_simp [hL.ne'] <;> ring
  rw [he] at hb
  calc
    _ ≤ C * Real.exp (-(1 / (8 * L)) * ρ ^ 2) * I := hb
    _ = (C * I) * Real.exp (-(1 / (8 * L)) * ρ ^ 2) := by ring
    _ ≤ (C * I + 1) * Real.exp (-(1 / (8 * L)) * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)

/-- Actual forward primitive-gradient decay at the same Gaussian width
as the primitive and terminal scalar errors. -/
theorem c19_forward_integrated_gradient_gaussian_decay
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ‖ζ‖ ≤ 2 →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ (ν : Fin d) (χ : C(Vec d, ℝ)), HasCompactSupport χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) →
    ∀ (fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
      (V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
        (χ x : ℂ) * (β ν + ζ • a ⟨0, by omega⟩ ν) (translate x ω)) →
      (∀ᵐ ω ∂reducedLaw Q,
        ∃ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup
            (ForcedLocality.retainedPair χ ω).1 ⟨0, by omega⟩ ζ Pr ∧
          ∀ s, V ω s = Pr s (fr ω)) →
    let H := fun j => ∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inl ν) j
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ J : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl)
        (∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal) J →
      Integrable (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ∑ j, ‖H j (translate x ω) - J j x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ∑ j, ‖H j (translate x ω) - J j x‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2) := by
  intro Λ
  obtain ⟨L, Ks, cs0, hL, hLp, hKs, hcs0, hscalar⟩ :=
    c19_forward_clock_primitive_terminal_gaussian_decay d hd D
  obtain ⟨Kf, cf, hKf, hcf, hforcing⟩ :=
    c19_forward_primitive_forcing_gaussian_decay hlocal d hd D L hLp
  let cs := cs0 / 16
  have hcs : 0 < cs := by dsimp only [cs]; positivity
  let B := 16 * Λ ^ 3 * (2 : ℝ) ^ 2 + 1
  let C := 4 * Λ * ((B + 9) * Ks + (4 * Λ + 16 / L + 1) * Kf)
  let c := min cs cf
  refine ⟨L, |C| + 1, c, hL, hLp, by positivity, lt_min hcs hcf, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag hζ G F hF ν χ hcχ hχb ρ hρ
    hplateau fr V hefr heV H
  let i : Fin d := ⟨0, by omega⟩
  let f := β ν + ζ • a i ν
  let u := ∫ s in Icc (0 : ℝ) 1, P s.toNNReal f
  let v := fun ω => ∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (zero_lt_one.trans_le Q.ellipticity_parameter)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsc := hscalar Q hQ β a μ hβ ha hμ ζ hζ P hP (.inl ν)
  have hfc := hforcing Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hF hζ
    (.inl ν) 1 (by norm_num)
  have hcoerc := c19_forward_integrated_gradient_gaussian_coercivity
    hd Q ζ P Pdag β a μ hP hPdag G F hF ν 1
  simp only [NNReal.coe_one, c19_unit_interval_integral_eq] at hcoerc
  have hsub := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (P 1 f - f)).measurable
    ((Lp.stronglyMeasurable (P 1 f)).measurable.sub (Lp.stronglyMeasurable f).measurable)
    (Lp.coeFn_sub (P 1 f) f)
  filter_upwards [hsc 1 (by norm_num), hsc 0 (by norm_num), hfc, hcoerc, hefr, heV, hsub,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) u,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (P 1 f - f)]
    with ω hc1 hc0 hfω hcω hinit hact hsubω hmu hmq
  obtain ⟨Pr, hPr, hVeq⟩ := hact
  have hs1 := hc1 χ (ρ / 4) (by positivity) hχb hcχ hplateau (fr ω) hinit Pr hPr
  have hs0 := hc0 χ (ρ / 4) (by positivity) hχb hcχ hplateau (fr ω) hinit Pr hPr
  have hv (s : ℝ) : Pr s.toNNReal (fr ω) = V ω s.toNNReal := (hVeq _).symm
  have hv1 : Pr 1 (fr ω) = V ω 1 := (hVeq _).symm
  have hv0 : V ω 0 = fr ω := by rw [hVeq, hPr.1]; rfl
  have hradius : -cs0 * (ρ / 4) ^ 2 = -cs * ρ ^ 2 := by dsimp only [cs]; ring
  rw [hradius] at hs1 hs0
  simp only [NNReal.coe_one, c19_unit_interval_integral_eq, Sum.elim_inl,
    hv, hv1, hPr.1, ContinuousLinearMap.id_apply] at hs1 hs0
  have hsinitial : Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖f (translate x ω) - fr ω x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖f (translate x ω) - fr ω x‖ ^ 2) ≤ Ks * Real.exp (-cs * ρ ^ 2) := by
    simpa only [f, i, hP.1, ContinuousLinearMap.id_apply] using hs0.2
  obtain ⟨J0, hJ0, hcoercive⟩ := hcω χ hχb Pr hPr (fr ω)
  obtain ⟨hfi, hdi, hfb⟩ := hfω χ ρ (zero_le_one.trans hρ) hχb
    (fun x hx => hplateau x hx.le)
  simp only [hv] at hJ0 hcoercive
  intro J hJ
  have he0 : J0 = J := physicalH1Graph_gradient_unique volume (Or.inl rfl) (v ω) J0 J hJ0 hJ
  rw [he0] at hcoercive
  let e : Vec d → ℂ := fun x => u (translate x ω) - v ω x
  let q : Vec d → ℂ := fun x => (P 1 f - f) (translate x ω) - (Pr 1 (fr ω) - fr ω) x
  have horbit : Measurable (fun x : Vec d => translate x ω) :=
    Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)
  have he : Measurable e :=
    ((Lp.stronglyMeasurable u).measurable.comp horbit).sub (Lp.stronglyMeasurable (v ω)).measurable
  have hq : Measurable q :=
    ((Lp.stronglyMeasurable (P 1 f - f)).measurable.comp horbit).sub
      (Lp.stronglyMeasurable (Pr 1 (fr ω) - fr ω)).measurable
  have hmU : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * e x) 2 volume := by
    simpa only [e, mul_sub, Pi.sub_def] using (hmu L hLp).sub
      (c19_gaussian_weight_memLp hLp (v ω))
  have hmQ : MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * q x) 2 volume := by
    simpa only [q, mul_sub, Pi.sub_def] using (hmq L hLp).sub
      (c19_gaussian_weight_memLp hLp (Pr 1 (fr ω) - fr ω))
  have hqi : Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2) := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hmQ.norm.integrable_sq
  have hpoint : ∀ᵐ x ∂volume, Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2 ≤
      2 * (Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P 1 f) (translate x ω) - V ω 1 x‖ ^ 2) +
      2 * (Real.exp (-euclideanSq x / L) ^ 2 *
        ‖f (translate x ω) - fr ω x‖ ^ 2) := by
    filter_upwards [hsubω, Lp.coeFn_sub (Pr 1 (fr ω)) (fr ω)] with x hx hy
    have hqeq : q x = ((P 1 f) (translate x ω) - V ω 1 x) -
        (f (translate x ω) - fr ω x) := by
      dsimp only [q]
      rw [hx, hy]
      simp only [Pi.sub_apply, hv1]
      ring
    rw [hqeq]
    have hn := norm_sub_le ((P 1 f) (translate x ω) - V ω 1 x)
      (f (translate x ω) - fr ω x)
    have hn2 : ‖((P 1 f) (translate x ω) - V ω 1 x) -
        (f (translate x ω) - fr ω x)‖ ^ 2 ≤
        2 * ‖(P 1 f) (translate x ω) - V ω 1 x‖ ^ 2 +
          2 * ‖f (translate x ω) - fr ω x‖ ^ 2 := by
      nlinarith only [hn, norm_nonneg (((P 1 f) (translate x ω) - V ω 1 x) -
        (f (translate x ω) - fr ω x)),
        sq_nonneg (‖(P 1 f) (translate x ω) - V ω 1 x‖ - ‖f (translate x ω) - fr ω x‖)]
    nlinarith only [mul_le_mul_of_nonneg_left hn2 (sq_nonneg
      (Real.exp (-euclideanSq x / L)))]
  have hqbound := integral_mono_ae hqi ((hs1.2.1.const_mul 2).add (hsinitial.1.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hqbound
  rw [integral_add (hs1.2.1.const_mul 2) (hsinitial.1.const_mul 2),
    integral_const_mul, integral_const_mul] at hqbound
  have hqbound' : (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖q x‖ ^ 2) ≤
      4 * Ks * Real.exp (-cs * ρ ^ 2) := by
    nlinarith only [hqbound, hs1.2.2, hsinitial.2]
  obtain ⟨hpairi, hpair⟩ := c19_gaussian_pairing_lower_bound hLp e q he hq hmU hmQ
  obtain ⟨hmomi, hmom⟩ := c19_gaussian_primitive_moment_bound hLp e he hmU
  have hscalarwide : (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖e x‖ ^ 2) ≤
      Ks * Real.exp (-cs * ρ ^ 2) := by
    simpa only [e, u, v, f, i] using hs1.1.2
  have hscalarnarrow := (c19_gaussian_energy_mono (show 0 < L / 2 by positivity)
    (show L / 2 ≤ L by linarith) e he hmU).2.trans hscalarwide
  have hcsrate : Real.exp (-cs * ρ ^ 2) ≤ Real.exp (-c * ρ ^ 2) :=
    Real.exp_le_exp.mpr (by
      simpa only [c, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left cs cf) (sq_nonneg ρ)))
  have hcfrate : Real.exp (-cf * ρ ^ 2) ≤ Real.exp (-c * ρ ^ 2) :=
    Real.exp_le_exp.mpr (by
      simpa only [c, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right cs cf) (sq_nonneg ρ)))
  have hscalarcommon := hscalarwide.trans (mul_le_mul_of_nonneg_left hcsrate hKs.le)
  have hqcommon := hqbound'.trans (mul_le_mul_of_nonneg_left hcsrate (by positivity : 0 ≤ 4 * Ks))
  have hforcecommon := hfb.trans (mul_le_mul_of_nonneg_left hcfrate hKf.le)
  have hζsq : ‖ζ‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith only [hζ, norm_nonneg ζ]
  have hcoef : 16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1 ≤ B := by
    dsimp only [B]
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hζsq
        (show 0 ≤ 16 * Λ ^ 3 by positivity)) 1
  have hmain := mul_le_mul hcoef
    (hscalarnarrow.trans (mul_le_mul_of_nonneg_left hcsrate hKs.le))
    (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hB
  obtain ⟨hJi, hWi, hcineq⟩ := hcoercive L (1 / 2) hL (by norm_num)
  have hw : L * (1 / 2 : ℝ) = L / 2 := by ring
  simp only [hw] at hcineq hJi
  have hJbound : (Λ⁻¹ / 4) * (∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
      ∑ j, ‖H j (translate x ω) - J j x‖ ^ 2) ≤
      ((B + 9) * Ks + (4 * Λ + 16 / L + 1) * Kf) * Real.exp (-c * ρ ^ 2) := by
    have hF0 : 0 ≤ ∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ∑ j, ‖C9ShortTimeLocality.retainedFluxDefect χ ω x
          (fun k => H k (translate x ω)) j‖ ^ 2 :=
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hD0 : 0 ≤ ∫ x, Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
        ‖C9ShortTimeLocality.retainedDriftDefect χ ω x
          (fun k => H k (translate x ω)) i ζ‖ ^ 2 :=
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hforce := mul_le_mul_of_nonneg_left hforcecommon
      (show 0 ≤ 4 * Λ + 16 / L + 1 by positivity)
    have hDpos := mul_nonneg (show 0 ≤ 4 * Λ + 16 / L by positivity) hD0
    change 2 * (∫ x, q x *
        (((Real.exp (-euclideanSq x / (L / 2)) ^ 2 : ℝ) : ℂ) * star (e x))).re +
      (∫ x, (-2 * euclideanSq x / (L * (1 / 2 : ℝ) ^ 2) *
        Real.exp (-euclideanSq x / (L / 2)) ^ 2) * ‖e x‖ ^ 2) + _ ≤ _ at hcineq
    rw [hw] at hmom
    simp only [NNReal.coe_one] at hforce
    dsimp only [Λ, H, e, u, v, f, i] at hcineq hforce hmain hpair hmom hscalarcommon hqcommon hF0 hDpos ⊢
    nlinarith only [hcineq, hforce, hmain, hpair, hmom, hscalarcommon, hqcommon, hF0, hDpos]
  have hmult := mul_le_mul_of_nonneg_left hJbound (show 0 ≤ 4 * Λ by positivity)
  have hinv : (4 * Λ) * (Λ⁻¹ / 4) = 1 := by field_simp [hΛ.ne']
  simp only [← mul_assoc, hinv, one_mul] at hmult
  refine ⟨hJi, hmult.trans ?_⟩
  change C * Real.exp (-c * ρ ^ 2) ≤ (|C| + 1) * Real.exp (-c * ρ ^ 2)
  exact mul_le_mul_of_nonneg_right (by linarith only [le_abs_self C]) (Real.exp_nonneg _)

/-- One locally measurable forward primitive and gradient recovery, using the
same retained semigroup as the actual forward Gaussian comparison. -/
theorem c19_local_forward_primitive_gradient_family {d : ℕ}
    (χ θ : C(Vec d, ℝ)) (hcχ : HasCompactSupport χ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (U W : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → θ x = 0) (hW : IsOpen W)
    (hinterior : ∀ x ∈ W, θ x = 1) (hχ : ∀ x, χ x ≠ 0 → x ∈ W)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (i j : Fin d) (ζ : ℂ) :
    let : MeasurableSpace (FieldPair d) := localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ H : FieldPair d → Vec d → Fin d → ℂ,
      Measurable fr ∧ Measurable (Function.uncurry V) ∧
      Measurable (fun p : FieldPair d × Vec d => H p.1 p.2) ∧
      (∀ ω, IsSmoothFieldPair ω →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) *
          ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
            (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ))) ∧
      (∀ (ω : FieldPair d) (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl)
          (∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal) K →
          (fun x => H ω x) =ᵐ[volume] (fun x k => K k x)) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          ∀ t, V ω t = Pr t (fr ω) := by
  let : MeasurableSpace (FieldPair d) := localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  obtain ⟨fr, V, hfr, hV, hefr, hactual⟩ :=
    short_time_forward_cutoff_measurable_evolution χ θ hcχ hθ U W hsupport hW
      hinterior hχ Λ hΛ i j ζ
  let v : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun ω => ∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal
  have hv : StronglyMeasurable v := by
    have hm : StronglyMeasurable (fun p : FieldPair d × ℝ => V p.1 p.2.toNNReal) :=
      hV.stronglyMeasurable.comp_measurable
        (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd))
    exact hm.integral_prod_right'
  obtain ⟨H, hH, heH⟩ := c19_stronglyMeasurable_physical_gradient_recovery v hv
  exact ⟨fr, V, H, hfr, hV, hH, hefr, heH, hactual⟩


/-- Recentring one jointly local spatial vector field transfers its integrated
spatial error to the Euclidean error of the local orthogonal projection.
The single spatial point is shared by all coordinates. -/
theorem c19_projection_error_of_joint_local_spatial_error
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Fin d → Lp ℂ 2 (reducedLaw Q))
    (U S : Set (Vec d)) (R : ℝ)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hS : ∀ᵐ x ∂ν, x ∈ S)
    (hshift : ∀ x ∈ S, ∀ y ∈ U, -x + y ∈ {z : Vec d | euclideanNorm z < R})
    (H : FieldPair d → Vec d → Fin d → ℂ)
    (hH : @Measurable (FieldPair d × Vec d) (Fin d → ℂ)
      (@Prod.instMeasurableSpace (FieldPair d) (Vec d) (localSigma U) inferInstance)
      inferInstance (fun p => H p.1 p.2))
    (hHb : Measurable (fun p : FieldPair d × Vec d => H p.1 p.2))
    (ε : ℝ)
    (hI : Integrable (fun p : Vec d × FieldPair d =>
      ∑ j, ‖f j (translate p.1 p.2) - H p.2 p.1 j‖ ^ 2) (ν.prod (reducedLaw Q)))
    (hbound : (∫ p : Vec d × FieldPair d,
      ∑ j, ‖f j (translate p.1 p.2) - H p.2 p.1 j‖ ^ 2
        ∂(ν.prod (reducedLaw Q))) ≤ ε) :
    Real.sqrt (∑ j, ‖f j - C9ShortTimeLocality.localProjection Q R (f j)‖ ^ 2) ≤
      2 * Real.sqrt ε := by
  classical
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let E : Vec d × FieldPair d → ℝ := fun p =>
    ∑ j, ‖f j (translate p.1 p.2) - H p.2 p.1 j‖ ^ 2
  let D : Vec d × FieldPair d → ℝ := fun p =>
    ∑ j, ‖f j p.2 - H (translate (-p.1) p.2) p.1 j‖ ^ 2
  have hmT : Measurable (fun p : Vec d × FieldPair d => translate (-p.1) p.2) :=
    Probability.continuous_translate.measurable.comp (measurable_fst.neg.prodMk measurable_snd)
  have hT := (MeasurePreserving.id ν).skew_product hmT
    (ae_of_all _ fun x => (measurePreserving_translate μ (reducedLaw_stationary Q) (-x)).map_eq)
  have heq : (fun p : Vec d × FieldPair d => E (p.1, translate (-p.1) p.2)) = D := by
    funext p
    dsimp only [E, D]
    rw [translate_add, add_neg_cancel, translate_zero]
  have hDI : Integrable D (ν.prod μ) := by
    rw [← heq]
    exact (hT.integrable_comp hI.aestronglyMeasurable).mpr hI
  have hDb : (∫ p, D p ∂(ν.prod μ)) ≤ ε := by
    have hm := hI.aestronglyMeasurable
    rw [← hT.map_eq] at hm
    have ht := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at ht
    change (∫ p, E p ∂(ν.prod μ)) =
      (∫ p, E (p.1, translate (-p.1) p.2) ∂(ν.prod μ)) at ht
    rw [← heq]
    exact ht.symm.trans_le hbound
  have hgood : ∀ᵐ x ∂ν, x ∈ S ∧ Integrable (fun ω => D (x, ω)) μ :=
    hS.and hDI.prod_right_ae
  obtain ⟨x, hx, hxb⟩ := exists_notMem_null_le_integral hDI.integral_prod_left
    (ae_iff.mp hgood)
  have hxgood : x ∈ S ∧ Integrable (fun ω => D (x, ω)) μ := by
    simpa only [Set.mem_setOf_eq, not_not] using hx
  have hxb' : (∫ ω, D (x, ω) ∂μ) ≤ ε := by
    exact hxb.trans (by rwa [integral_prod _ hDI] at hDb)
  let v₀ : Fin d → FieldPair d → ℂ := fun j ω => H (translate (-x) ω) x j
  have hvlocal (j : Fin d) :
      Measurable[localSigma {z : Vec d | euclideanNorm z < R}] (v₀ j) :=
    ((measurable_pi_apply j).comp hH).comp
      ((measurable_translate_localSigma (-x) (hshift x hxgood.1)).prodMk measurable_const)
  have hvb (j : Fin d) : Measurable (v₀ j) :=
    ((measurable_pi_apply j).comp hHb).comp
      ((Probability.measurable_translate (-x)).prodMk measurable_const)
  have hdiff (j : Fin d) : Integrable (fun ω => ‖f j ω - v₀ j ω‖ ^ 2) μ := by
    apply hxgood.2.mono'
      (((Lp.stronglyMeasurable (f j)).measurable.sub (hvb j)).norm.pow_const 2).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change ‖f j ω - v₀ j ω‖ ^ 2 ≤ ∑ k, ‖f k ω - v₀ k ω‖ ^ 2
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖f k ω - v₀ k ω‖)
      (Finset.mem_univ j)
  have hvm (j : Fin d) : MemLp (v₀ j) 2 μ := by
    have he : MemLp (fun ω => f j ω - v₀ j ω) 2 μ :=
      (memLp_two_iff_integrable_sq_norm
        (((Lp.stronglyMeasurable (f j)).measurable.sub (hvb j)).aestronglyMeasurable)).mpr
          (hdiff j)
    have heq' : (fun ω => f j ω - (f j ω - v₀ j ω)) =ᵐ[μ] v₀ j :=
      ae_of_all _ fun ω => sub_sub_cancel (f j ω) (v₀ j ω)
    exact (memLp_congr_ae heq').mp ((Lp.memLp (f j)).sub he)
  let v : Fin d → Lp ℂ 2 μ := fun j => (hvm j).toLp (v₀ j)
  have hv (j : Fin d) : IsComplexLocalObservation Q R (v j) :=
    ⟨v₀ j, hvlocal j, (hvm j).coeFn_toLp.symm⟩
  have he (j : Fin d) : (fun ω => (f j - v j) ω) =ᵐ[μ]
      (fun ω => f j ω - v₀ j ω) := by
    filter_upwards [Lp.coeFn_sub (f j) (v j), (hvm j).coeFn_toLp] with ω h1 h2
    have h2' : v j ω = v₀ j ω := h2
    exact h1.trans (congrArg (fun z : ℂ => f j ω - z) h2')
  have hnorm (j : Fin d) : ‖f j - v j‖ ^ 2 = ∫ ω, ‖f j ω - v₀ j ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    exact integral_congr_ae ((he j).mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)
  have hsum : (∑ j, ‖f j - v j‖ ^ 2) ≤ ε := by
    simp_rw [hnorm]
    rw [← integral_finsetSum _ (fun j _ => hdiff j)]
    exact hxb'
  exact (C9ShortTimeLocality.euclidean_sub_localProjection_le Q R f v hv).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (by norm_num))

/-- A samplewise Gaussian energy bound yields one local Euclidean projection
bound. The averaging window is fixed before the law and shared by all entries. -/
theorem c19_projection_error_of_gaussian_local_error
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Fin d → Lp ℂ 2 (reducedLaw Q)) (U S : Set (Vec d)) (R σ ε : ℝ)
    (hσ : 0 < σ) (hS : MeasurableSet S) (hvol : 0 < volume S)
    (hvoltop : volume S ≠ ∞) (hsmall : ∀ x ∈ S, euclideanSq x ≤ 1)
    (hshift : ∀ x ∈ S, ∀ y ∈ U, -x + y ∈ {z : Vec d | euclideanNorm z < R})
    (H : FieldPair d → Vec d → Fin d → ℂ)
    (hH : @Measurable (FieldPair d × Vec d) (Fin d → ℂ)
      (@Prod.instMeasurableSpace (FieldPair d) (Vec d) (localSigma U) inferInstance)
      inferInstance (fun p => H p.1 p.2))
    (hHb : Measurable (fun p : FieldPair d × Vec d => H p.1 p.2))
    (herror : ∀ᵐ ω ∂reducedLaw Q,
      Integrable (fun x => Real.exp (-euclideanSq x / σ) ^ 2 *
        ∑ j, ‖f j (translate x ω) - H ω x j‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / σ) ^ 2 *
        ∑ j, ‖f j (translate x ω) - H ω x j‖ ^ 2) ≤ ε) :
    Real.sqrt (∑ j, ‖f j - C9ShortTimeLocality.localProjection Q R (f j)‖ ^ 2) ≤
      2 * Real.sqrt ((Real.exp (2 / σ) / (volume S).toReal) * ε) := by
  classical
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let ν := PDE.normalizedVolumeOn S
  let : IsProbabilityMeasure ν :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hvol
      (lt_top_iff_ne_top.mpr hvoltop)
  let A := Real.exp (2 / σ)
  let C := A / (volume S).toReal
  let E : FieldPair d × Vec d → ℝ := fun p =>
    ∑ j, ‖f j (translate p.2 p.1) - H p.1 p.2 j‖ ^ 2
  have hE : Measurable E := by
    apply Finset.measurable_sum
    intro j _
    exact (((Lp.stronglyMeasurable (f j)).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_fst))).sub
          ((measurable_pi_apply j).comp hHb)).norm.pow_const 2
  have hE0 (ω : FieldPair d) (x : Vec d) : 0 ≤ E (ω, x) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hweight (x : Vec d) (hx : x ∈ S) :
      1 ≤ A * Real.exp (-euclideanSq x / σ) ^ 2 := by
    change 1 ≤ Real.exp (2 / σ) * Real.exp (-euclideanSq x / σ) ^ 2
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp
    have he : 2 / σ + (2 : ℕ) * (-euclideanSq x / σ) =
        2 * (1 - euclideanSq x) / σ := by ring
    rw [he]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hsmall x hx))) hσ.le
  have hper : ∀ᵐ ω ∂μ, Integrable (fun x => E (ω, x)) ν ∧
      (∫ x, E (ω, x) ∂ν) ≤ C * ε := by
    filter_upwards [herror] with ω hω
    have hi : IntegrableOn (fun x => E (ω, x)) S := by
      apply (hω.1.restrict.const_mul A).mono'
        ((hE.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      filter_upwards [ae_restrict_mem hS] with x hx
      change ‖E (ω, x)‖ ≤ A * (Real.exp (-euclideanSq x / σ) ^ 2 * E (ω, x))
      rw [Real.norm_of_nonneg (hE0 ω x)]
      have hh := mul_le_mul_of_nonneg_right (hweight x hx) (hE0 ω x)
      simpa only [one_mul, mul_assoc] using hh
    have hb : (∫ x in S, E (ω, x)) ≤ A * ε := by
      calc
        _ ≤ ∫ x in S, A * (Real.exp (-euclideanSq x / σ) ^ 2 * E (ω, x)) := by
          apply integral_mono_ae hi (hω.1.restrict.const_mul A)
          filter_upwards [ae_restrict_mem hS] with x hx
          have hh := mul_le_mul_of_nonneg_right (hweight x hx) (hE0 ω x)
          simpa only [one_mul, mul_assoc] using hh
        _ = A * ∫ x in S, Real.exp (-euclideanSq x / σ) ^ 2 * E (ω, x) :=
          integral_const_mul _ _
        _ ≤ A * ∫ x, Real.exp (-euclideanSq x / σ) ^ 2 * E (ω, x) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact integral_mono_measure Measure.restrict_le_self
            (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (hE0 ω x)) hω.1
        _ ≤ A * ε := mul_le_mul_of_nonneg_left hω.2 (Real.exp_nonneg _)
    refine ⟨PDE.integrable_normalizedVolumeOn_of_integrableOn hi hvol, ?_⟩
    change (∫ x, E (ω, x) ∂((volume S)⁻¹ • volume.restrict S)) ≤ C * ε
    rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
    calc
      _ ≤ (volume S).toReal⁻¹ * (A * ε) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * ε := by dsimp only [C]; ring
  have hI : Integrable E (μ.prod ν) := by
    apply (integrable_prod_iff hE.aestronglyMeasurable).mpr
    refine ⟨hper.mono fun _ h => h.1, ?_⟩
    apply (integrable_const (C * ε)).mono'
      (hE.norm.aestronglyMeasurable.integral_prod_right')
    filter_upwards [hper] with ω hω
    simp_rw [Real.norm_of_nonneg (hE0 ω _)]
    rw [Real.norm_of_nonneg (integral_nonneg fun x => hE0 ω x)]
    exact hω.2
  apply c19_projection_error_of_joint_local_spatial_error Q f U S R ν
    (Measure.ae_smul_measure (ae_restrict_mem hS) (volume S)⁻¹) hshift H hH hHb
    (C * ε) hI.swap
  change (∫ p : Vec d × FieldPair d, (E ∘ Prod.swap) p ∂(ν.prod μ)) ≤ C * ε
  rw [integral_prod_symm _ hI.swap]
  calc
    _ ≤ ∫ ω, C * ε ∂μ :=
      integral_mono_ae hI.integral_prod_left (integrable_const _) (hper.mono fun _ h => h.2)
    _ = C * ε := by simp


/-- The supplied forward observation has its literal spatial coefficient datum
on one event, with the signed complex force preserved. -/
theorem c19_forward_spatial_datum {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (i j : Fin d) (ζ : ℂ) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (β j + ζ • a i j : Lp ℂ 2 (reducedLaw Q)) (translate x ω) =
        ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
          (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x i j : ℂ)) := by
  have hsum : (β j + ζ • a i j : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      (fun ω => β j ω + ζ * a i j ω) := by
    filter_upwards [Lp.coeFn_add (β j) (ζ • a i j), Lp.coeFn_smul ζ (a i j)]
      with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply]
    rfl
  have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (β j + ζ • a i j)).measurable
    ((Lp.stronglyMeasurable (β j)).measurable.add
      ((Lp.stronglyMeasurable (a i j)).measurable.const_mul ζ)) hsum
  have ha' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (a i j)).measurable
    (by fun_prop : Measurable (fun ω : FieldPair d => (ω.1 0 i j : ℂ))) (ha i j)
  filter_upwards [hs, ha', short_time_transpose_drift_spatial_identification hβ j]
    with ω hsω haω hβω
  filter_upwards [hsω, haω, hβω] with x h1 h2 h3
  simpa only [translate_matrix, add_zero, h3] using
    h1.trans (congrArg (fun z : ℂ => β j (translate x ω) + ζ * z) h2)

/-- Actual retained forward and transpose primitives produce one jointly local
vector field with a samplewise Gaussian error bound. The width and decay
constants are structural and are chosen before the environment law. -/
theorem c19_actual_local_primitive_gradient_comparison
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ σ K c : ℝ, 0 < σ ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ‖ζ‖ ≤ 2 →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ (ν : FluxIndex d) (ρ : ℝ), 1 ≤ ρ →
    ∃ H : FieldPair d → Vec d → Fin d → ℂ,
      @Measurable _ _
        ((localSigma {x : Vec d | euclideanNorm x < ρ}).prod inferInstance)
        inferInstance (fun p : FieldPair d × Vec d => H p.1 p.2) ∧
      Measurable (fun p : FieldPair d × Vec d => H p.1 p.2) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        Integrable (fun x => Real.exp (-euclideanSq x / σ) ^ 2 *
          ∑ j, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal ν j) (translate x ω) - H ω x j‖ ^ 2) ∧
        (∫ x, Real.exp (-euclideanSq x / σ) ^ 2 *
          ∑ j, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal ν j) (translate x ω) - H ω x j‖ ^ 2) ≤
          K * Real.exp (-c * ρ ^ 2) := by
  classical
  obtain ⟨L, Kf, cf, hL, hLp, hKf, hcf, hf⟩ :=
    c19_forward_integrated_gradient_gaussian_decay hlocal d hd D
  obtain ⟨Cχ, hCχ, hcut⟩ := short_time_compatible_euclidean_cutoffs d
  obtain ⟨Kt, ct, hKt, hct, ht⟩ :=
    c19_transpose_integrated_gradient_gaussian_decay d hd D L hL hLp Cχ hCχ.le
  refine ⟨L / 2, Kf + Kt, min cf ct, by positivity, by positivity, lt_min hcf hct, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd hζ G F hF ν ρ hρ
  let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hΛ : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (by linarith [Q.ellipticity_parameter])) Q.ellipticity_parameter
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  obtain ⟨χ, θ, hχ, hθ, hcχ, hcθ, hχb, hθb, hχone, hχzero, hθzero,
    hθone, hχsupport, hθsupport, hχder, hθder⟩ := hcut ρ hρp
  let U := {x : Vec d | euclideanNorm x < ρ}
  have hmId : @Measurable (FieldPair d) (FieldPair d) inferInstance (localSigma U) id :=
    fun s hs => Probability.localSigma_le_borel U s hs
  have hmProd : @Measurable (FieldPair d × Vec d) (FieldPair d × Vec d)
      inferInstance ((localSigma U).prod inferInstance) id :=
    (hmId.comp measurable_fst).prodMk measurable_snd
  have hbf : Kf * Real.exp (-cf * ρ ^ 2) ≤
      (Kf + Kt) * Real.exp (-min cf ct * ρ ^ 2) := by
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
    nlinarith [min_le_left cf ct, sq_nonneg ρ]
  have hbt : Kt * Real.exp (-ct * ρ ^ 2) ≤
      (Kf + Kt) * Real.exp (-min cf ct * ρ ^ 2) := by
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
    nlinarith [min_le_right cf ct, sq_nonneg ρ]
  obtain ⟨M, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  cases ν with
  | inl j =>
      obtain ⟨fr, V, H, hfr, hV, hH, hefr, heH, hactual⟩ :=
        c19_local_forward_primitive_gradient_family χ θ hcχ hθ U
          {x : Vec d | euclideanNorm x < ρ / 2} hθsupport
          (isOpen_lt Entropy.continuous_euclideanNorm' continuous_const)
          (fun x hx => hθone x hx.le) hχsupport Λ hΛ ⟨0, by omega⟩ j ζ
      have hHb : Measurable (fun p : FieldPair d × Vec d => H p.1 p.2) := hH.comp hmProd
      have hact : ∀ᵐ ω ∂reducedLaw Q,
          ∃ Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
              Lp ℂ 2 (volume : Measure (Vec d)),
            IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1
              ⟨0, by omega⟩ ζ Pr ∧ ∀ s, V ω s = Pr s (fr ω) := by
        filter_upwards [c19_retained_coefficients_admissible Q] with ω hω
        exact hactual ω (hω χ hχb).2
      have hinit : ∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume]
          fun x => (χ x : ℂ) * (β j + ζ • a ⟨0, by omega⟩ j) (translate x ω) := by
        filter_upwards [hsmooth Q hQ, c19_forward_spatial_datum hβ ha ⟨0, by omega⟩ j ζ]
          with ω hsω hfω
        filter_upwards [hefr ω hsω.1, hfω] with x h1 h2
        rw [h1, h2]
      have hdec := hf Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd hζ G F hF
        j χ hcχ hχb ρ hρ hχone fr V hinit hact
      have hcoerc := c19_forward_integrated_gradient_gaussian_coercivity
        hd Q ζ P Pdag β a μ hP hPd G F hF j 1
      simp only [NNReal.coe_one, c19_unit_interval_integral_eq] at hcoerc
      refine ⟨H, hH, hHb, ?_⟩
      filter_upwards [hdec, hcoerc, hact] with ω hdω hcω haω
      obtain ⟨Pr, hPr, hVeq⟩ := haω
      obtain ⟨J, hJ, _⟩ := hcω χ hχb Pr hPr (fr ω)
      have hJ' : IsPhysicalH1Graph volume (Or.inl rfl)
          (∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal) J := by
        simpa only [hVeq] using hJ
      obtain ⟨hi, hb⟩ := hdω J hJ'
      have he : (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
          ∑ k, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inl j) k) (translate x ω) - H ω x k‖ ^ 2)
          =ᵐ[volume] (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
            ∑ k, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inl j) k) (translate x ω) - J k x‖ ^ 2) :=
        (heH ω J hJ').mono fun x hx => by
          change H ω x = (fun k => J k x) at hx
          exact congrArg (fun v : Fin d → ℂ =>
            Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
              ∑ k, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inl j) k) (translate x ω) - v k‖ ^ 2) hx
      exact ⟨hi.congr he.symm, (integral_congr_ae he).trans_le (hb.trans hbf)⟩
  | inr u =>
      cases u
      have hsupport : ∀ x, x ∉ U → χ x = 0 := by
        intro x hx
        exact hχzero x (by have hh : ρ ≤ euclideanNorm x := not_lt.mp hx; linarith)
      obtain ⟨fr, V, H, hfr, hV, hH, hefr, heH, hactual⟩ :=
        c19_local_transpose_primitive_gradient_family χ hχ hcχ U hsupport Λ hΛ ⟨0, by omega⟩ ζ
      have hHb : Measurable (fun p : FieldPair d × Vec d => H p.1 p.2) := hH.comp hmProd
      let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
      let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
      have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
      have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) := Lp.SecondCountableTopology
      have hfrb : StronglyMeasurable fr := (hfr.comp hmId).stronglyMeasurable
      have hVb : StronglyMeasurable (Function.uncurry V) :=
        (hV.comp ((hmId.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
      have hact : ∀ᵐ ω ∂reducedLaw Q,
          ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
              Lp ℂ 2 (volume : Measure (Vec d)),
            IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1
              ⟨0, by omega⟩ ζ Pr Tr ∧ ∀ s, V ω s = Tr s (fr ω) := by
        filter_upwards [c19_retained_coefficients_admissible Q] with ω hω
        obtain ⟨Pr, Tr, hPr, hTr, _, _, heV⟩ := hactual ω (hω χ hχb).2
        exact ⟨Pr, Tr, hTr, heV⟩
      have hinit : ∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume]
          fun x => (((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
            (fun y => (ForcedLocality.retainedPair χ ω).1 y k ⟨0, by omega⟩) x : ℝ) : ℂ) := by
        filter_upwards [hsmooth Q hQ] with ω hsω
        exact hefr ω hsω.1
      have hplateau : ∀ x, euclideanSq x < (ρ / 4) ^ 2 → χ x = 1 := by
        intro x hx
        apply hχone
        change Real.sqrt (euclideanSq x) ≤ ρ / 4
        exact (Real.sqrt_le_iff).mpr ⟨by positivity, hx.le⟩
      have hdec := ht Q hQ β a μ hβ ζ P Pdag hP hPd hζ G F hF χ hχ hχb
        ρ hρ hplateau hχzero hχder fr V hfrb hVb hinit hact
      have hcoerc := c19_transpose_integrated_gradient_gaussian_coercivity
        hd Q ζ P Pdag β a μ hP hPd G F hF 1
      simp only [NNReal.coe_one, c19_unit_interval_integral_eq] at hcoerc
      refine ⟨H, hH, hHb, ?_⟩
      filter_upwards [hdec, hcoerc, hact] with ω hdω hcω haω
      obtain ⟨Pr, Tr, hTr, hVeq⟩ := haω
      obtain ⟨J, hJ, _⟩ := hcω χ hχb Pr Tr hTr (fr ω)
      have hJ' : IsPhysicalH1Graph volume (Or.inl rfl)
          (∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal) J := by
        simpa only [hVeq] using hJ
      obtain ⟨hi, hb⟩ := hdω J hJ'
      have he : (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
          ∑ k, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inr ()) k) (translate x ω) - H ω x k‖ ^ 2)
          =ᵐ[volume] (fun x => Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
            ∑ k, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inr ()) k) (translate x ω) - J k x‖ ^ 2) :=
        (heH ω J hJ').mono fun x hx => by
          change H ω x = (fun k => J k x) at hx
          exact congrArg (fun v : Fin d → ℂ =>
            Real.exp (-euclideanSq x / (L / 2)) ^ 2 *
              ∑ k, ‖(∫ s in Icc (0 : ℝ) 1, G s.toNNReal (.inr ()) k) (translate x ω) - v k‖ ^ 2) hx
      exact ⟨hi.congr he.symm, (integral_congr_ae he).trans_le (hb.trans hbt)⟩

/-- The first-unit integrated actual flux has structural Gaussian locality in
the Euclidean norm, uniformly in every supplied admissible environment law. -/
theorem c19_first_unit_integrated_gradient_projection_error :
    ∀ (hlocal : node_l_u3A_forced_u2D_localStmt)
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 2 →
    ∀ (ν : FluxIndex d) (n : ℕ), 1 ≤ n →
      Real.sqrt (∑ j : Fin d,
        ‖(∫ s in Set.Icc (0 : ℝ) 1, G s.toNNReal ν j) -
          C9ShortTimeLocality.localProjection Q (C * (n : ℝ))
            (∫ s in Set.Icc (0 : ℝ) 1, G s.toNNReal ν j)‖ ^ 2) ≤
        C * Real.exp (-c * (n : ℝ) ^ 2) := by
  intro hlocal d hd D
  obtain ⟨σ, K, c₀, hσ, hK, hc₀, hlocalerror⟩ :=
    c19_actual_local_primitive_gradient_comparison hlocal d hd D
  let S := PDE.euclideanBall (0 : PDE.Vec d) 1
  let A := Real.exp (2 / σ) / (volume S).toReal
  let C := 2 + 2 * Real.sqrt (A * K)
  have hA : 0 < A := div_pos (Real.exp_pos _) (ENNReal.toReal_pos
    (PDE.volume_euclideanBall_pos _ zero_lt_one).ne'
    (PDE.volume_euclideanBall_ne_top _ zero_le_one))
  have hC : 2 ≤ C := by dsimp only [C]; linarith [Real.sqrt_nonneg (A * K)]
  refine ⟨C, c₀ / 2, by linarith, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨H, hH, hHb, he⟩ := hlocalerror Q hQ β a μ hβ ha hμ ζ P Pdag
    hP hPd hζ G F hF ν (n : ℝ) hn'
  have hsq : ∀ x ∈ S, euclideanSq x < 1 := by
    intro x hx
    simpa only [S, PDE.euclideanBall, Set.mem_setOf_eq, PDE.euclideanSqDist,
      sub_zero, PDE.vecNormSq, PDE.vecDot, euclideanSq, dot, one_pow] using hx
  have hsmall : ∀ x ∈ S, euclideanSq x ≤ 1 := fun x hx => (hsq x hx).le
  have hshift : ∀ x ∈ S, ∀ y ∈ {z : Vec d | euclideanNorm z < (n : ℝ)},
      -x + y ∈ {z : Vec d | euclideanNorm z < C * (n : ℝ)} := by
    intro x hx y hy
    have hx' : euclideanNorm x < 1 := by
      change Real.sqrt (euclideanSq x) < 1
      exact (Real.sqrt_lt' zero_lt_one).mpr (by simpa only [one_pow] using hsq x hx)
    have htri := TimeChange.euclideanNorm_add_le (-x) y
    rw [Entropy.euclideanNorm_neg'] at htri
    change euclideanNorm y < (n : ℝ) at hy
    change euclideanNorm (-x + y) < C * (n : ℝ)
    nlinarith
  have hp := c19_projection_error_of_gaussian_local_error Q
    (fun j => ∫ s in Icc (0 : ℝ) 1, G s.toNNReal ν j)
    {x : Vec d | euclideanNorm x < (n : ℝ)} S (C * (n : ℝ)) σ
    (K * Real.exp (-c₀ * (n : ℝ) ^ 2)) hσ
    (PDE.isOpen_euclideanBall _ _).measurableSet
    (PDE.volume_euclideanBall_pos _ zero_lt_one)
    (PDE.volume_euclideanBall_ne_top _ zero_le_one) hsmall hshift H hH hHb he
  apply hp.trans
  change 2 * Real.sqrt (A * (K * Real.exp (-c₀ * (n : ℝ) ^ 2))) ≤
    C * Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2)
  have hexp : Real.sqrt (Real.exp (-c₀ * (n : ℝ) ^ 2)) =
      Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) := by
    rw [← Real.exp_half]
    congr 1
    ring
  rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hA.le hK.le), hexp]
  calc
    _ = (2 * Real.sqrt (A * K)) * Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) := by ring
    _ ≤ C * Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
        (Real.exp_nonneg _)

end EinsteinFull.Blueprint
