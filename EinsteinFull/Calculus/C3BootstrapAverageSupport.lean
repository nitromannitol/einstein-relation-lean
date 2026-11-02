import EinsteinFull.Calculus.C3SmoothedDuhamelClosureSupport
import EinsteinFull.Calculus.C1BootstrapAverageSupport
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Strong convergence of a locally uniformly bounded operator family permits
its argument to vary. Operator-norm continuity is not required. -/
theorem c3Tendsto_operator_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} {l : Filter ι} {A : ι → E →L[ℝ] F} {A₀ : E →L[ℝ] F}
    {u : ι → E} {u₀ : E} (hu : Tendsto u l (𝓝 u₀))
    (hA : ∀ v, Tendsto (fun t => A t v) l (𝓝 (A₀ v)))
    (C : ℝ) (hC : ∀ᶠ t in l, ‖A t‖ ≤ C) :
    Tendsto (fun t => A t (u t)) l (𝓝 (A₀ u₀)) := by
  have hz : Tendsto (fun t => A t (u t - u₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun t => C * ‖u t - u₀‖) l (𝓝 0) from by
      simpa only [sub_self, norm_zero, mul_zero] using
        tendsto_const_nhds.mul (hu.sub_const u₀).norm)
    filter_upwards [hC] with t ht
    exact (A t).le_opNorm (u t - u₀) |>.trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have hh := hz.add (hA u₀)
  simpa only [map_sub, sub_add_cancel, zero_add] using hh

/-- A product rule for strong operator curves, using only a uniform local
operator bound and the strong derivatives at fixed vectors. -/
theorem c3HasDerivAt_operator_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℝ → E →L[ℝ] F} {u : ℝ → E} {u' : E} {v' : F} {t : ℝ}
    (hu : HasDerivAt u u' t)
    (hA : ∀ v, ContinuousAt (fun r => A r v) t)
    (hv : HasDerivAt (fun r => A r (u t)) v' t)
    (C : ℝ) (hC : ∀ᶠ r in 𝓝 t, ‖A r‖ ≤ C) :
    HasDerivAt (fun r => A r (u r)) (A t u' + v') t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hs := c3Tendsto_operator_apply hu.tendsto_slope
    (fun v => (hA v).mono_left nhdsWithin_le_nhds) C
    (hC.filter_mono nhdsWithin_le_nhds)
  have hh := hs.add hv.tendsto_slope
  apply hh.congr'
  exact Eventually.of_forall fun r => by
    simp only [slope_def_module, map_smul, map_sub]
    rw [← smul_add]
    congr 1
    abel

/-- The actual homogeneous interaction curve, smoothed at a fixed positive
spatial scale. Its terminal value is the smoothed physical endpoint. -/
def c3BootstrapInteraction {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ξ : ℂ) (s : ℝ) (hs : 0 < s)
    (U : ℝ → Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) : Lp ℂ 2 (reducedLaw Q) :=
  homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ (T - t).toNNReal
    (gaussianAverage hd Q s hs (U t))

/-- The interaction is strongly differentiable at every interior time where
the physical endpoint is differentiable. Strong operator continuity suffices. -/
theorem c3BootstrapInteraction_differentiableAt {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ξ : ℂ) (s : ℝ) (hs : 0 < s)
    (U : ℝ → Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) (htT : t < T)
    (hU : DifferentiableAt ℝ U t) :
    DifferentiableAt ℝ (c3BootstrapInteraction hd Q ξ s hs U T) t := by
  let A := fun v : ℝ => (homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ
    (T - v).toNNReal).restrictScalars ℝ
  let u := fun v : ℝ => gaussianAverage hd Q s hs (U v)
  have hu : DifferentiableAt ℝ u t :=
    ((homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0).restrictScalars ℝ).differentiableAt.comp
      t hU
  have hA (f : Lp ℂ 2 (reducedLaw Q)) : ContinuousAt (fun v => A v f) t :=
    ((continuous_homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ f).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))).continuousAt
  have hv := (hasDerivAt_homogeneousGaussianEvolution_time Q ⟨0, by omega⟩ ξ
    (u t) (T - t) (sub_pos.mpr htT)).scomp t ((hasDerivAt_id t).const_sub T)
  let B := fun v : ℝ => Real.exp
    (sourceReducedBound Λ * ‖ξ‖ ^ 2 * ((T - v).toNNReal : ℝ) / 2)
  have hBc : Continuous B := by unfold B; fun_prop
  have hB : ∀ᶠ v in 𝓝 t, ‖A v‖ ≤ B t + 1 := by
    filter_upwards [hBc.continuousAt.eventually (eventually_lt_nhds (lt_add_one (B t)))] with v hv
    have hn : ‖A v‖ ≤ B v := by
      simpa only [A, ContinuousLinearMap.norm_restrictScalars] using
        norm_homogeneousGaussianEvolution_le Q ⟨0, by omega⟩ ξ (T - v).toNNReal
    exact hn.trans hv.le
  exact (c3HasDerivAt_operator_apply hu.hasDerivAt hA hv (B t + 1) hB).differentiableAt

/-- Bilinear transposition of the all-time evolution, including time zero. -/
theorem c3EndpointPairing_homogeneousEvolution {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ξ : ℂ) (t : ℝ≥0)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (homogeneousGaussianEvolution Q i ξ t f) g =
      c4EndpointPairing Q f (homogeneousGaussianEvolution Q i (-ξ) t g) := by
  by_cases ht : 0 < (t : ℝ)
  · simp only [homogeneousGaussianEvolution_pos Q i ξ t ht,
      homogeneousGaussianEvolution_pos Q i (-ξ) t ht]
    exact c4EndpointPairing_homogeneousAverage Q i t ht ξ f g
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp ht) t.coe_nonneg)
    simp only [ht0, homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply]

/-- The strong interaction curve is precisely the physical weak interaction,
with its signed force and literal Gaussian averaging. -/
theorem c3BootstrapInteraction_pairing {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ξ : ℂ) (s : ℝ) (hs : 0 < s)
    (U : ℝ → Lp ℂ 2 (reducedLaw Q)) (T t : ℝ)
    (g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (c3BootstrapInteraction hd Q ξ s hs U T t) g =
      c4EndpointPairing Q (U t) (homogeneousGaussianEvolution Q ⟨0, by omega⟩
        (-ξ) (T - t).toNNReal (gaussianAverage hd Q s hs g)) := by
  rw [c3BootstrapInteraction, c3EndpointPairing_homogeneousEvolution]
  change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (U t)) _ = _
  rw [c4EndpointPairing_homogeneousAverage, neg_zero]
  congr 1
  change gaussianAverage hd Q s hs
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - t).toNNReal g) = _
  simpa only [c3GaussianDerivativeAverage_zero] using
    c3GaussianDerivativeAverage_homogeneousEvolution hd Q ⟨0, by omega⟩ (-ξ)
      (T - t).toNNReal s hs 0 (fun j => Fin.elim0 j) g

/-- Strong continuity at the terminal time follows from the actual endpoint
continuity and the uniform structural operator bound. -/
theorem c3BootstrapInteraction_continuousAt {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ξ : ℂ) (s : ℝ) (hs : 0 < s)
    (U : ℝ → Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) (hU : ContinuousAt U t) :
    ContinuousAt (c3BootstrapInteraction hd Q ξ s hs U T) t := by
  let A := fun v : ℝ => (homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ
    (T - v).toNNReal).restrictScalars ℝ
  let u := fun v : ℝ => gaussianAverage hd Q s hs (U v)
  have hu : ContinuousAt u t :=
    ((homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0).restrictScalars ℝ).continuous.continuousAt.comp hU
  have hA (f : Lp ℂ 2 (reducedLaw Q)) : ContinuousAt (fun v => A v f) t :=
    ((continuous_homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ f).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))).continuousAt
  let B := fun v : ℝ => Real.exp
    (sourceReducedBound Λ * ‖ξ‖ ^ 2 * ((T - v).toNNReal : ℝ) / 2)
  have hBc : Continuous B := by unfold B; fun_prop
  have hB : ∀ᶠ v in 𝓝 t, ‖A v‖ ≤ B t + 1 := by
    filter_upwards [hBc.continuousAt.eventually (eventually_lt_nhds (lt_add_one (B t)))] with v hv
    have hn : ‖A v‖ ≤ B v := by
      simpa only [A, ContinuousLinearMap.norm_restrictScalars] using
        norm_homogeneousGaussianEvolution_le Q ⟨0, by omega⟩ ξ (T - v).toNNReal
    exact hn.trans hv.le
  exact c3Tendsto_operator_apply hu hA (B t + 1) hB

section PhysicalInteraction
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
    (G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hflux : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t))

local notation "U" => (fun t : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ (Real.toNNReal t))
local notation "ξ" => ((endpointDriftSign ν : ℂ) * ζ)

include hc hQ hβ ha hμ hP hPdag hflux

/-- The strong derivative of the actual interaction is the physical backward
flux functional in every L2 pairing. The equation is used only through the
unconditional centered-endpoint derivative theorem. -/
theorem c3BootstrapInteraction_deriv_pairing
    (s : ℝ) (hs : 0 < s) (T t : ℝ) (ht : 0 < t) (htT : t < T)
    (g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (deriv (c3BootstrapInteraction hd Q ξ s hs U T) t) g =
      c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t := by
  have hU := c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν t ht
  have hF := c3BootstrapInteraction_differentiableAt hd Q ξ s hs U T t htT hU
  have htest := (((c4EndpointPairing Q).flip g).hasFDerivAt).comp_hasDerivAt t hF.hasDerivAt
  have hphysical := c3CenteredEndpoint_backward_flux_hasDerivAt
    hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux
    (gaussianAverage hd Q s hs g) T t ht htT
  have heq : (fun v => c4EndpointPairing Q
      (c3BootstrapInteraction hd Q ξ s hs U T v) g) =
      (fun v => c4EndpointPairing Q (U v)
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ)
          (T - v).toNNReal (gaussianAverage hd Q s hs g))) := by
    funext v
    exact c3BootstrapInteraction_pairing hd Q ξ s hs U T v g
  rw [← heq] at hphysical
  exact htest.unique hphysical

/-- A scalar majorant of all physical pairings gives Bochner time integrability
of the actual strong derivative. No time measurability of a chosen flux family
is assumed. -/
theorem c3BootstrapInteraction_deriv_intervalIntegrable
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (B : ℝ → ℝ) (hBi : IntervalIntegrable B volume τ T)
    (hBpos : ∀ t ∈ Set.Ioo τ T, 0 ≤ B t)
    (hB : ∀ (g : Lp ℂ 2 (reducedLaw Q)), ∀ t ∈ Set.Ioo τ T,
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
        B t * ‖g‖) :
    IntervalIntegrable (deriv (c3BootstrapInteraction hd Q ξ s hs U T)) volume τ T := by
  apply hBi.mono_fun' (aestronglyMeasurable_deriv _ _)
  change ∀ᵐ t ∂volume.restrict (Set.uIoc τ T),
    ‖deriv (c3BootstrapInteraction hd Q ξ s hs U T) t‖ ≤ B t
  rw [Set.uIoc_of_le hτT.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ae_restrict_iff' measurableSet_Ioo]
  apply Eventually.of_forall
  intro t ht
  apply c3Norm_le_of_endpointPairing_bound Q _ (hBpos t ht)
  intro g
  rw [c3BootstrapInteraction_deriv_pairing hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν G J hflux s hs T t (hτ.trans ht.1) ht.2 g]
  exact hB g t ht

/-- The actual homogeneous smoothed mild identity in the reduced L2 space.
The weak-FTC pairing engine is lifted to a genuine Bochner integral and the
upper endpoint is evaluated from strong continuity of the actual evolution. -/
theorem c3BootstrapInteraction_mild_of_flux_bound
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (B : ℝ → ℝ) (hBi : IntervalIntegrable B volume τ T)
    (hBpos : ∀ t ∈ Set.Ioo τ T, 0 ≤ B t)
    (hB : ∀ (g : Lp ℂ 2 (reducedLaw Q)), ∀ t ∈ Set.Ioo τ T,
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
        B t * ‖g‖) :
    IntervalIntegrable (deriv (c3BootstrapInteraction hd Q ξ s hs U T)) volume τ T ∧
    gaussianAverage hd Q s hs (U T) -
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ (T - τ).toNNReal
        (gaussianAverage hd Q s hs (U τ)) =
      ∫ t in τ..T, deriv (c3BootstrapInteraction hd Q ξ s hs U T) t := by
  have hi := c3BootstrapInteraction_deriv_intervalIntegrable hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν G J hflux s hs T τ hτ hτT B hBi hBpos hB
  refine ⟨hi, ?_⟩
  have hdF (t : ℝ) (ht : t ∈ Set.Ioo τ T) :=
    (c3BootstrapInteraction_differentiableAt hd Q ξ s hs U T t ht.2
      (c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
        ζ P Pdag hP hPdag ν t (hτ.trans ht.1))).hasDerivAt
  have hleft := c3BootstrapInteraction_continuousAt hd Q ξ s hs U T τ
    (c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν τ hτ).continuousAt
  have hright := c3BootstrapInteraction_continuousAt hd Q ξ s hs U T T
    (c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν T (hτ.trans hτT)).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hτT hdF hi
    (hleft.mono_left nhdsWithin_le_nhds) (hright.mono_left nhdsWithin_le_nhds)
  simpa only [c3BootstrapInteraction, sub_self, Real.toNNReal_zero,
    homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply] using hFTC.symm

end PhysicalInteraction
/-- Integrating in the actual L2 space preserves an integrably bounded higher
Lp norm. The higher-Lp lift is measurable by the injective probability-law
inclusion, rather than by a separate regularity hypothesis on the time flux. -/
theorem c3Integral_memLp_of_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    (f : α → Lp ℂ 2 (reducedLaw Q)) (hf : Integrable f ρ)
    (hfp : ∀ᵐ t ∂ρ, MemLp (f t : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q))
    (B : α → ℝ) (hBi : Integrable B ρ)
    (hB : ∀ᵐ t ∂ρ,
      (eLpNorm (f t : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B t) :
    MemLp ((∫ t, f t ∂ρ : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm ((∫ t, f t ∂ρ : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ ∫ t, B t ∂ρ := by
  classical
  have := reducedLaw_probability Q
  let q := ENNReal.ofReal p
  have hq : 2 ≤ q := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  have : Fact (q ≠ ∞) := ⟨ENNReal.ofReal_ne_top⟩
  let : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let : PolishSpace (FieldPair d) := inferInstance
  borelize ↥(Lp ℂ q (reducedLaw Q))
  borelize ↥(Lp ℂ 2 (reducedLaw Q))
  let v : α → Lp ℂ q (reducedLaw Q) := fun t =>
    if h : MemLp (f t : FieldPair d → ℂ) q (reducedLaw Q) then h.toLp (f t) else 0
  let inc := complexLpToL2CLM (reducedLaw Q) hq
  have hinc : ∀ᵐ t ∂ρ, inc (v t) = f t := by
    filter_upwards [hfp] with t ht
    dsimp only [v]
    rw [dite_eq_left ht]
    exact Lp.ext ht.coeFn_toLp
  have hme : MeasurableEmbedding inc :=
    inc.continuous.measurableEmbedding (complexLpToL2_injective (reducedLaw Q) hq)
  have hvm : AEStronglyMeasurable v ρ :=
    (hme.aemeasurable_comp_iff.mp (hf.aestronglyMeasurable.aemeasurable.congr (Filter.EventuallyEq.symm hinc))).aestronglyMeasurable
  have hvB : ∀ᵐ t ∂ρ, ‖v t‖ ≤ B t := by
    filter_upwards [hfp, hB] with t ht hBt
    dsimp only [v]
    rw [dite_eq_left ht, Lp.norm_def, eLpNorm_congr_ae ht.coeFn_toLp]
    exact hBt
  have hvi : Integrable v ρ := hBi.mono' hvm hvB
  have heq : inc (∫ t, v t ∂ρ) = ∫ t, f t ∂ρ := by
    rw [← inc.integral_comp_comm hvi]
    exact integral_congr_ae hinc
  rw [← heq]
  refine ⟨Lp.memLp (∫ t, v t ∂ρ), ?_⟩
  change ‖∫ t, v t ∂ρ‖ ≤ _
  exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hvi.norm hBi hvB)

/-- Finite physical L2 sums obey their higher-Lp triangle bound, by lifting
all summands through the injective probability-law inclusion. -/
theorem c3Lp_linearCombination_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    {ι : Type*} [Fintype ι] (f : ι → Lp ℂ 2 (reducedLaw Q))
    (g : Lp ℂ 2 (reducedLaw Q)) (a : ℝ) (c : ℂ)
    (hf : ∀ j, MemLp (f j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q))
    (hg : MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) :
    let v := a • (∑ j, f j) + c • g
    MemLp (v : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (v : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        ‖a‖ * (∑ j, (eLpNorm (f j : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal) +
        ‖c‖ * (eLpNorm (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  classical
  have := reducedLaw_probability Q
  let q := ENNReal.ofReal p
  have hq : 2 ≤ q := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  let f' : ι → Lp ℂ q (reducedLaw Q) := fun j => (hf j).toLp (f j)
  let g' := hg.toLp g
  let inc := complexLpToL2CLM (reducedLaw Q) hq
  have hfi : ∀ j, inc (f' j) = f j := fun j => Lp.ext (hf j).coeFn_toLp
  have hgi : inc g' = g := Lp.ext hg.coeFn_toLp
  have heq : inc (a • (∑ j, f' j) + c • g') = a • (∑ j, f j) + c • g := by
    have hai : inc (a • (∑ j, f' j)) = a • inc (∑ j, f' j) :=
      (inc.restrictScalars ℝ).map_smul a _
    rw [map_add, hai, map_sum, map_smul, hgi]
    simp only [hfi]
  dsimp only
  rw [← heq]
  refine ⟨(Lp.memLp (a • (∑ j, f' j) + c • g')), ?_⟩
  change ‖a • (∑ j, f' j) + c • g'‖ ≤ _
  calc
    _ ≤ ‖a • (∑ j, f' j)‖ + ‖c • g'‖ := norm_add_le _ _
    _ = ‖a‖ * ‖∑ j, f' j‖ + ‖c‖ * ‖g'‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖a‖ * (∑ j, ‖f' j‖) + ‖c‖ * ‖g'‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg a)) le_rfl
    _ = _ := by
      have hfn : ∀ j, ‖f' j‖ = (eLpNorm (f j : FieldPair d → ℂ) q (reducedLaw Q)).toReal := by
        intro j
        rw [Lp.norm_def, eLpNorm_congr_ae (hf j).coeFn_toLp]
      simp only [hfn]
      rw [Lp.norm_def, eLpNorm_congr_ae hg.coeFn_toLp]

/-- The actual homogeneous evolution preserves higher Lp, with its exact
Gaussian mass factor and leading coefficient one, including time zero. -/
theorem c3HomogeneousEvolution_memLp {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (p : ℝ) (hp : 2 ≤ p) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) :
    MemLp (homogeneousGaussianEvolution Q i ζ t f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (homogeneousGaussianEvolution Q i ζ t f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.exp (ζ.im ^ 2 * (t : ℝ) * homogenizedCoefficient Q i i / 2) *
        (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  by_cases ht : 0 < (t : ℝ)
  · simpa only [homogeneousGaussianEvolution_pos Q i ζ t ht] using
      bootstrap_average_homogeneous_Lp Q i t ht ζ p hp f hf
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt ht) t.coe_nonneg)
    subst t
    simpa only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply,
      NNReal.coe_zero, mul_zero, zero_mul, zero_div, Real.exp_zero, one_mul] using
      (show MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal from
        ⟨hf, le_rfl⟩)

/-- Complex scalars can be moved out of the physical bilinear pairing. -/
theorem c3EndpointPairing_complex_smul {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (c : ℂ) (f g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (c • f) g = c * c4EndpointPairing Q f g := by
  rw [c4EndpointPairing_apply, c4EndpointPairing_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with ω hω
  simp only [hω, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The physical smoothed forcing propagated to the terminal time. This uses
only the centered actual flux, with the signed force of the endpoint. -/
def c3BootstrapFluxVector {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (T t : ℝ) : Lp ℂ 2 (reducedLaw Q) :=
  (1 / 2 : ℝ) • (∑ j : Fin d,
    homogeneousGaussianEvolution Q ⟨0, by omega⟩ ((endpointDriftSign ν : ℂ) * ζ)
      (T - t).toNNReal (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
        (centeredComplexLp Q (J t.toNNReal j)))) +
  c4EndpointSourceCoefficient ν ζ •
    c3BootstrapInteraction hd Q ((endpointDriftSign ν : ℂ) * ζ) s hs
      (fun v => centeredComplexLp Q (J v.toNNReal ⟨0, by omega⟩)) T t

/-- Higher-Lp control of the physical vector forcing from the smoothed
centered flux components. The homogeneous mass factor is retained exactly. -/
theorem c3BootstrapFluxVector_memLp {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (T t : ℝ) (p : ℝ) (hp : 2 ≤ p) (C₀ C₁ : ℝ)
    (hzero : MemLp
      (gaussianAverage hd Q s hs (centeredComplexLp Q (J t.toNNReal ⟨0, by omega⟩)) :
        FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q))
    (hone : ∀ j, MemLp
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
        (centeredComplexLp Q (J t.toNNReal j)) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q))
    (hzeroB : (eLpNorm
      (gaussianAverage hd Q s hs (centeredComplexLp Q (J t.toNNReal ⟨0, by omega⟩)) :
        FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C₀)
    (honeB : ∀ j, (eLpNorm
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
        (centeredComplexLp Q (J t.toNNReal j)) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C₁) :
    MemLp (c3BootstrapFluxVector hd Q ν ζ J s hs T t : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (c3BootstrapFluxVector hd Q ν ζ J s hs T t : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.exp (((endpointDriftSign ν : ℂ) * ζ).im ^ 2 *
        ((T - t).toNNReal : ℝ) * homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2) *
          ((1 / 2 : ℝ) * d * C₁ + ‖c4EndpointSourceCoefficient ν ζ‖ * C₀) := by
  classical
  let ξ := (endpointDriftSign ν : ℂ) * ζ
  let E := Real.exp (ξ.im ^ 2 * ((T - t).toNNReal : ℝ) *
    homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2)
  let f := fun j => gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
    (centeredComplexLp Q (J t.toNNReal j))
  let g := gaussianAverage hd Q s hs (centeredComplexLp Q (J t.toNNReal ⟨0, by omega⟩))
  let A := homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ (T - t).toNNReal
  have hder := fun j => c3HomogeneousEvolution_memLp Q ⟨0, by omega⟩ ξ
    (T - t).toNNReal p hp (f j) (hone j)
  have hsrc := c3HomogeneousEvolution_memLp Q ⟨0, by omega⟩ ξ
    (T - t).toNNReal p hp g hzero
  have hc := c3Lp_linearCombination_bound Q p hp (fun j => A (f j)) (A g)
    (1 / 2) (c4EndpointSourceCoefficient ν ζ) (fun j => (hder j).1) hsrc.1
  have hhalf : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [hhalf] at hc
  refine ⟨hc.1, hc.2.trans ?_⟩
  have hderB : ∀ j, (eLpNorm (A (f j) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ E * C₁ := fun j =>
    (hder j).2.trans (mul_le_mul_of_nonneg_left (honeB j) (Real.exp_pos _).le)
  have hsrcB : (eLpNorm (A g : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ E * C₀ :=
    hsrc.2.trans (mul_le_mul_of_nonneg_left hzeroB (Real.exp_pos _).le)
  calc
    _ ≤ (1 / 2 : ℝ) * (∑ _j : Fin d, E * C₁) +
        ‖c4EndpointSourceCoefficient ν ζ‖ * (E * C₀) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => hderB j)) (by norm_num))
        (mul_le_mul_of_nonneg_left hsrcB (norm_nonneg _))
    _ = E * ((1 / 2 : ℝ) * d * C₁ + ‖c4EndpointSourceCoefficient ν ζ‖ * C₀) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The vector flux has exactly the physical backward pairing, including the
integration-by-parts sign and the centered source. -/
theorem c3BootstrapFluxVector_pairing {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (T t : ℝ) (ht : t < T)
    (g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (c3BootstrapFluxVector hd Q ν ζ J s hs T t) g =
      c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t := by
  classical
  let F := fun j => centeredComplexLp Q (J t.toNNReal j)
  let ξ := -((endpointDriftSign ν : ℂ) * ζ)
  let W := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ (T - t)
    (sub_pos.mpr ht) ξ (gaussianAverage hd Q s hs g)
  let w := homogeneousAverage Q ⟨0, by omega⟩ (T - t)
    (sub_pos.mpr ht) ξ (gaussianAverage hd Q s hs g)
  have hW := homogeneousAverage_hasComplexHorizontalGradient_allData Q
    ⟨0, by omega⟩ (T - t) (sub_pos.mpr ht) ξ (gaussianAverage hd Q s hs g)
  have hsum : (∫ ω, ∑ j, J t.toNNReal j ω * W j ω ∂reducedLaw Q) =
      -(∑ j, c4EndpointPairing Q
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ ((endpointDriftSign ν : ℂ) * ζ)
          (T - t).toNNReal
          (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j))) g) := by
    rw [integral_finsetSum _ (fun j _ => integrable_complexLp_mul Q (J t.toNNReal j) (W j)),
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← c4EndpointPairing_apply,
      c3EndpointPairing_centered_gradient Q w W hW _ j]
    have hg := c3EndpointPairing_homogeneousSmoothedGradient hd Q ⟨0, by omega⟩ ξ
      (T - t).toNNReal (Real.toNNReal_pos.mpr (sub_pos.mpr ht)) s hs (F j) g j
    simp only [Real.coe_toNNReal _ (sub_pos.mpr ht).le] at hg
    simpa only [ξ, neg_neg] using hg
  have hsource : (∫ ω, (J t.toNNReal ⟨0, by omega⟩ ω -
      ∫ ω', J t.toNNReal ⟨0, by omega⟩ ω' ∂reducedLaw Q) * w ω ∂reducedLaw Q) =
      c4EndpointPairing Q (F ⟨0, by omega⟩) w := by
    rw [c4EndpointPairing_apply]
    apply integral_congr_ae
    filter_upwards [coeFn_centeredComplexLp Q (J t.toNNReal ⟨0, by omega⟩)] with ω hω
    rw [hω]
  have hsource' : c4EndpointPairing Q
      (c3BootstrapInteraction hd Q ((endpointDriftSign ν : ℂ) * ζ) s hs
        (fun v => centeredComplexLp Q (J v.toNNReal ⟨0, by omega⟩)) T t) g =
      c4EndpointPairing Q (F ⟨0, by omega⟩) w := by
    rw [c3BootstrapInteraction_pairing]
    congr 1
    have hw := homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ ξ
      (T - t).toNNReal (Real.toNNReal_pos.mpr (sub_pos.mpr ht))
      (gaussianAverage hd Q s hs g)
    simp only [Real.coe_toNNReal _ (sub_pos.mpr ht).le] at hw
    exact hw
  rw [c3BootstrapFluxVector, map_add, add_apply,
    c3EndpointPairing_complex_smul, hsource', map_smul, smul_apply,
    map_sum, sum_apply]
  rw [c3BackwardFluxFunctional, dite_eq_left ht]
  change (1 / 2 : ℝ) • (∑ j, c4EndpointPairing Q _ g) +
    c4EndpointSourceCoefficient ν ζ * c4EndpointPairing Q (F ⟨0, by omega⟩) w =
      -(1 / 2 : ℂ) * (∫ ω, ∑ j, J t.toNNReal j ω * W j ω ∂reducedLaw Q) +
      c4EndpointSourceCoefficient ν ζ *
        (∫ ω, (J t.toNNReal ⟨0, by omega⟩ ω -
          ∫ ω', J t.toNNReal ⟨0, by omega⟩ ω' ∂reducedLaw Q) * w ω ∂reducedLaw Q)
  rw [hsum, hsource]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, neg_mul_neg]
  rfl

section PhysicalFluxIdentification
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
    (G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hflux : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t))

local notation "U" => (fun t : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ (Real.toNNReal t))
local notation "ξ" => ((endpointDriftSign ν : ℂ) * ζ)

include hc hQ hβ ha hμ hP hPdag hflux


/-- The actual strong interaction derivative equals the actual propagated
smoothed flux. This identity supplies higher-Lp control of the Bochner
integrand without any chosen time-regularity premise on the flux. -/
theorem c3BootstrapInteraction_deriv_eq_flux
    (s : ℝ) (hs : 0 < s) (T t : ℝ) (ht : 0 < t) (htT : t < T) :
    deriv (c3BootstrapInteraction hd Q ξ s hs U T) t =
      c3BootstrapFluxVector hd Q ν ζ J s hs T t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply c3Norm_le_of_endpointPairing_bound Q _ le_rfl
  intro g
  rw [map_sub, sub_apply,
    c3BootstrapInteraction_deriv_pairing hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν G J hflux s hs T t ht htT g,
    c3BootstrapFluxVector_pairing hd Q ν ζ J s hs T t htT g,
    sub_self, norm_zero, zero_mul]

/-- An integrable higher-Lp flux bound yields the same bound for the actual
mild remainder. Time measurability is derived internally from the strong
interaction derivative, even when the given flux family has no regularity. -/
theorem c3BootstrapInteraction_mild_Lp_bound
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (p : ℝ) (hp : 2 ≤ p) (B : ℝ → ℝ) (hBi : IntervalIntegrable B volume τ T)
    (hBpos : ∀ t ∈ Set.Ioo τ T, 0 ≤ B t)
    (hfp : ∀ t ∈ Set.Ioo τ T,
      MemLp (c3BootstrapFluxVector hd Q ν ζ J s hs T t : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q))
    (hB : ∀ t ∈ Set.Ioo τ T,
      (eLpNorm (c3BootstrapFluxVector hd Q ν ζ J s hs T t : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B t) :
    let remainder := gaussianAverage hd Q s hs (U T) -
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ (T - τ).toNNReal
        (gaussianAverage hd Q s hs (U τ))
    MemLp (remainder : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (remainder : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        ∫ t in τ..T, B t := by
  have := reducedLaw_probability Q
  let q := ENNReal.ofReal p
  have hq : 2 ≤ q := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  have hnorm (t : ℝ) (ht : t ∈ Set.Ioo τ T) :
      ‖c3BootstrapFluxVector hd Q ν ζ J s hs T t‖ ≤ B t := by
    let v := c3BootstrapFluxVector hd Q ν ζ J s hs T t
    have hi : complexLpToL2 (reducedLaw Q) hq ((hfp t ht).toLp v) = v :=
      Lp.ext (hfp t ht).coeFn_toLp
    calc
      ‖v‖ = ‖complexLpToL2 (reducedLaw Q) hq ((hfp t ht).toLp v)‖ := congrArg norm hi.symm
      _ ≤ ‖(hfp t ht).toLp v‖ := norm_complexLpToL2_le _ hq _
      _ = (eLpNorm (v : FieldPair d → ℂ) q (reducedLaw Q)).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae (hfp t ht).coeFn_toLp]
      _ ≤ B t := hB t ht
  have hpair (g : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : t ∈ Set.Ioo τ T) :
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
        B t * ‖g‖ := by
    rw [← c3BootstrapFluxVector_pairing hd Q ν ζ J s hs T t ht.2 g]
    exact (c3EndpointPairing_norm_le Q _ g).trans
      (mul_le_mul_of_nonneg_right (hnorm t ht) (norm_nonneg g))
  have hmild := c3BootstrapInteraction_mild_of_flux_bound hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν G J hflux s hs T τ hτ hτT B hBi hBpos hpair
  have hAE : ∀ᵐ t ∂volume.restrict (Set.Ioc τ T), t ∈ Set.Ioo τ T := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hdmem : ∀ᵐ t ∂volume.restrict (Set.Ioc τ T),
      MemLp ((deriv (c3BootstrapInteraction hd Q ξ s hs U T) t : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ)
        q (reducedLaw Q) := by
    filter_upwards [hAE] with t ht
    rw [c3BootstrapInteraction_deriv_eq_flux hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν G J hflux s hs T t (hτ.trans ht.1) ht.2]
    exact hfp t ht
  have hdB : ∀ᵐ t ∂volume.restrict (Set.Ioc τ T),
      (eLpNorm ((deriv (c3BootstrapInteraction hd Q ξ s hs U T) t : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ)
        q (reducedLaw Q)).toReal ≤ B t := by
    filter_upwards [hAE] with t ht
    rw [c3BootstrapInteraction_deriv_eq_flux hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν G J hflux s hs T t (hτ.trans ht.1) ht.2]
    exact hB t ht
  have hi := c3Integral_memLp_of_bound Q p hp (volume.restrict (Set.Ioc τ T))
    (deriv (c3BootstrapInteraction hd Q ξ s hs U T)) hmild.1.1 hdmem B hBi.1 hdB
  dsimp only
  rw [hmild.2, intervalIntegral.integral_of_le hτT.le]
  simpa only [intervalIntegral.integral_of_le hτT.le] using hi

/-- One physical averaged-bootstrap step, with coefficient one on the actual
homogeneous evolution. All time integrability is derived from the endpoint
equation; only the higher-Lp bounds themselves enter this estimate. -/
theorem c3BootstrapInteraction_half_step
    (s : ℝ) (hs : 0 < s) (t : ℝ) (ht : 0 < t)
    (p : ℝ) (hp : 2 ≤ p) (H B : ℝ) (hBpos : 0 ≤ B)
    (hinitial : MemLp (gaussianAverage hd Q s hs (U (t / 2)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q))
    (hH : (eLpNorm (gaussianAverage hd Q s hs (U (t / 2)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ H)
    (hfp : ∀ r ∈ Set.Ioo (t / 2) t,
      MemLp (c3BootstrapFluxVector hd Q ν ζ J s hs t r : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q))
    (hB : ∀ r ∈ Set.Ioo (t / 2) t,
      (eLpNorm (c3BootstrapFluxVector hd Q ν ζ J s hs t r : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B) :
    MemLp (gaussianAverage hd Q s hs (U t) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (gaussianAverage hd Q s hs (U t) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.exp (((endpointDriftSign ν : ℂ) * ζ).im ^ 2 * (t / 2) *
        homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2) * H + (t / 2) * B := by
  have hrem := c3BootstrapInteraction_mild_Lp_bound hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν G J hflux s hs t (t / 2) (half_pos ht) (by linarith)
    p hp (fun _ => B) intervalIntegrable_const (fun _ _ => hBpos) hfp hB
  dsimp only at hrem
  let v := homogeneousGaussianEvolution Q ⟨0, by omega⟩ ξ (t - t / 2).toNNReal
    (gaussianAverage hd Q s hs (U (t / 2)))
  let R := gaussianAverage hd Q s hs (U t) - v
  have hv := c3HomogeneousEvolution_memLp Q ⟨0, by omega⟩ ξ
    (t - t / 2).toNNReal p hp _ hinitial
  have hsum := c3Lp_linearCombination_bound Q p hp (fun _ : Unit => v) R 1 1
    (fun _ => hv.1) hrem.1
  have hsum' : MemLp ((v + R : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm ((v + R : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (eLpNorm (v : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (eLpNorm (R : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, norm_one, one_mul, one_smul]
      using hsum
  have hcancel : v + R = gaussianAverage hd Q s hs (U t) := by dsimp only [R]; abel
  rw [hcancel] at hsum'
  refine ⟨hsum'.1, hsum'.2.trans (add_le_add ?_ ?_)⟩
  · have htime : ((t - t / 2).toNNReal : ℝ) = t / 2 := by
      rw [Real.coe_toNNReal _ (by linarith)]
      ring
    exact hv.2.trans (by
      rw [htime]
      exact mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le)
  · dsimp only [R, v]
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      show t - t / 2 = t / 2 by ring] using hrem.2

end PhysicalFluxIdentification


/-- The structural Gaussian rate controls either physical drift sign. -/
theorem c3Bootstrap_gaussian_rate_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ν : EndpointIndex d) (ζ : ℂ)
    (growth : ℝ) (hgrowth : sourceReducedBound Λ ≤ growth) :
    ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 * homogenizedCoefficient Q i i / 2 ≤
      growth * ‖ζ‖ ^ 2 / 2 := by
  have he : |homogenizedCoefficient Q i i| ≤ sourceReducedBound Λ := by
    have hc (x : Vec d) : |x i| ≤ euclideanNorm x := by
      apply Real.le_sqrt_of_sq_le
      simpa only [euclideanSq, dot, ← pow_two, sq_abs] using
        Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    have h := (hc ((homogenizedCoefficient Q).mulVec (unitVector i))).trans
      (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i)
    simpa only [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  have hsign : ‖(endpointDriftSign ν : ℂ) * ζ‖ = ‖ζ‖ := by
    rcases ν with j | v
    · simp only [endpointDriftSign, Complex.ofReal_one, one_mul]
    · cases v <;> simp only [endpointDriftSign, Complex.ofReal_one, one_mul,
        Complex.ofReal_neg, neg_mul, norm_neg]
  have him : ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 ≤ ‖ζ‖ ^ 2 := by
    rw [← hsign]
    nlinarith only [Complex.sq_norm_sub_sq_im ((endpointDriftSign ν : ℂ) * ζ),
      sq_nonneg (((endpointDriftSign ν : ℂ) * ζ).re)]
  have hcoeff := (le_abs_self (homogenizedCoefficient Q i i)).trans he
  have hfirst := mul_le_mul_of_nonneg_left hcoeff
    (sq_nonneg (((endpointDriftSign ν : ℂ) * ζ).im))
  have hsecond := mul_le_mul_of_nonneg_left him ((abs_nonneg _).trans he)
  have hthird := mul_le_mul_of_nonneg_right hgrowth (sq_nonneg ‖ζ‖)
  nlinarith only [hfirst, hsecond, hthird]

/-- Each coordinate is bounded by the actual Euclidean square sum. -/
theorem c3Bootstrap_coordinate_le_sqrt_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (j : ι) : f j ≤ Real.sqrt (∑ i, (f i) ^ 2) := by
  classical
  exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun i _ => sq_nonneg (f i))
    (Finset.mem_univ j))

/-- The terminal force restriction supplies the wider flux window at every
intermediate time. The structural exponent is chosen before moment parameters. -/
theorem c3Bootstrap_force_window (m r F η ηflux : ℝ)
    (hm : 0 ≤ m) (hr : 1 ≤ r) (hrF : r ≤ F)
    (hηhalf : η ≤ 1 / 2) (hηflux : η ≤ ηflux)
    (hterminal : m * Real.sqrt F ≤ F ^ η) :
    m * Real.sqrt r ≤ r ^ ηflux := by
  exact (scalar_force_window_mono m r F η hm (by linarith) hrF hηhalf hterminal).trans
    (Real.rpow_le_rpow_of_exponent_le hr hηflux)

/-- An unrestricted smoothing scale above b times the terminal time bounds
the polynomial flux loss uniformly on the integration interval. -/
theorem c3Bootstrap_polynomial_loss (b t r s : ℝ) (L : ℕ)
    (hb : 0 < b) (ht : 0 < t) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hs : b * t ≤ s) :
    (1 + r / s) ^ L ≤ (1 + b⁻¹) ^ L := by
  have hspos : 0 < s := (mul_pos hb ht).trans_le hs
  have hratio : r / s ≤ b⁻¹ := by
    apply (div_le_iff₀ hspos).2
    have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hb.le)
    rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul] at h
    exact hrt.trans h
  exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hratio) L

/-- Forward Gaussian growth and the half-time flux exponential fit inside
the terminal weight without increasing the earlier averaged coefficient. -/
theorem c3Bootstrap_exponential_loss (A g t r : ℝ)
    (hA : A ≤ g / 2) (hg : 0 ≤ g) (hr : 0 ≤ r) (hrt : r ≤ t) :
    Real.exp (A * (t - r)) * Real.exp (g * r / 2) ≤ Real.exp (g * t) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hrt)
  have hgt : 0 ≤ g * t := mul_nonneg hg (hr.trans hrt)
  nlinarith only [h, hgt]

/-- A constant majorant on the last half interval controls all real smoothing
scales s ≥ b t, including s larger than the terminal time. -/
theorem c3Bootstrap_flux_majorant (A g C K b t r s ε q : ℝ) (L : ℕ)
    (hA : A ≤ g / 2) (hg : 0 ≤ g) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : 0 < b) (ht : 0 < t) (hr : t / 2 ≤ r) (hrt : r ≤ t)
    (hs : b * t ≤ s) (hε : 0 ≤ ε) :
    Real.exp (A * (t - r)) *
        (C * K * Real.exp (g * r / 2) * r ^ (-1 - ε) * s ^ q * (1 + r / s) ^ L) ≤
      C * K * Real.exp (g * t) * (t / 2) ^ (-1 - ε) * s ^ q * (1 + b⁻¹) ^ L := by
  have hrpos : 0 < r := (half_pos ht).trans_le hr
  have hspos : 0 < s := (mul_pos hb ht).trans_le hs
  have he := c3Bootstrap_exponential_loss A g t r hA hg hrpos.le hrt
  have hp := Real.rpow_le_rpow_of_nonpos (half_pos ht) hr
    (show -1 - ε ≤ 0 by linarith)
  have hl := c3Bootstrap_polynomial_loss b t r s L hb ht hrpos.le hrt hs
  calc
    _ = C * K * (Real.exp (A * (t - r)) * Real.exp (g * r / 2)) *
        r ^ (-1 - ε) * s ^ q * (1 + r / s) ^ L := by ring
    _ ≤ C * K * Real.exp (g * t) * (t / 2) ^ (-1 - ε) * s ^ q *
        (1 + b⁻¹) ^ L := by
      apply mul_le_mul _ hl (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hspos.le q)
      exact mul_le_mul (mul_le_mul_of_nonneg_left he (mul_nonneg hC hK)) hp
        (Real.rpow_nonneg hrpos.le _) (by positivity)

/-- Integrating the constant last-half-interval majorant leaves exactly a
power gain, with no loss depending on the integration time. -/
theorem c3Bootstrap_half_integral (t ε M : ℝ) (ht : 0 < t) :
    (∫ _r in t / 2..t, M * (t / 2) ^ (-1 - ε)) =
      2 ^ ε * t ^ (-ε) * M := by
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have hpow : (t / 2) * (t / 2) ^ (-1 - ε) = (t / 2) ^ (-ε) := by
    conv_lhs => lhs; rw [← Real.rpow_one (t / 2)]
    rw [← Real.rpow_add (half_pos ht)]
    congr 1
    ring
  calc
    _ = ((t / 2) * (t / 2) ^ (-1 - ε)) * M := by ring
    _ = (t / 2) ^ (-ε) * M := by rw [hpow]
    _ = 2 ^ ε * t ^ (-ε) * M := by
      rw [Real.div_rpow ht.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
      ring

/-- The physical centered source coefficient has at most the force norm. -/
theorem c3Bootstrap_source_norm_le {d : ℕ} (ν : EndpointIndex d) (ζ : ℂ) :
    ‖c4EndpointSourceCoefficient ν ζ‖ ≤ ‖ζ‖ := by
  rcases ν with j | v
  · exact le_rfl
  · cases v
    · exact le_rfl
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (norm_nonneg ζ)

/-- The actual propagated flux has a constant higher-Lp majorant throughout
the last half interval. Both derivative orders use their own polynomial loss. -/
theorem c3BootstrapFluxVector_uniform_bound {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (t r b ε growth K p : ℝ) (L : ℕ → ℕ)
    (Cder : ℕ → ℝ) (hp : 2 ≤ p) (ht : 0 < t) (hr : t / 2 ≤ r) (hrt : r ≤ t)
    (hb : 0 < b) (hbs : b * t ≤ s) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCder : ∀ k, 0 ≤ Cder k) (hgrowth : 0 ≤ growth)
    (hrate : sourceReducedBound Λ ≤ growth)
    (hflux : ∀ k : ℕ, ∀ dirs : Fin k → Fin d,
      (∀ j, MemLp
        (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J r.toNNReal j)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
      Real.sqrt (∑ j, ((eLpNorm
        (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J r.toNNReal j)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤
        Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * r / 2) *
          r ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + r / s) ^ L k) :
    MemLp (c3BootstrapFluxVector hd Q ν ζ J s hs t r : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (c3BootstrapFluxVector hd Q ν ζ J s hs t r : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.exp (growth * ‖ζ‖ ^ 2 * t) * (t / 2) ^ (-1 - ε) * K *
        ((d : ℝ) / 2 * Cder 1 * (1 + b⁻¹) ^ L 1 * s ^ (-(d : ℝ) / 4 - 1 / 2) +
          ‖ζ‖ * Cder 0 * (1 + b⁻¹) ^ L 0 * s ^ (-(d : ℝ) / 4)) := by
  let C := fun k => Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * r / 2) *
    r ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + r / s) ^ L k
  have hcomp (k : ℕ) (dirs : Fin k → Fin d) (j : Fin d) :
      (eLpNorm (gaussianDerivativeAverage hd Q s hs k dirs
        (centeredComplexLp Q (J r.toNNReal j)) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C k :=
    (c3Bootstrap_coordinate_le_sqrt_sum _ j).trans (hflux k dirs).2
  have hzero := hflux 0 (fun j => Fin.elim0 j)
  have hzeroB := hcomp 0 (fun j => Fin.elim0 j) ⟨0, by omega⟩
  simp only [c3GaussianDerivativeAverage_zero] at hzero hzeroB
  have hv := c3BootstrapFluxVector_memLp hd Q ν ζ J s hs t r p hp (C 0) (C 1)
    (hzero.1 ⟨0, by omega⟩) (fun j => (hflux 1 (fun _ => j)).1 j)
    hzeroB (fun j => hcomp 1 (fun _ => j) j)
  refine ⟨hv.1, hv.2.trans ?_⟩
  let A := ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 * homogenizedCoefficient Q
    ⟨0, by omega⟩ ⟨0, by omega⟩ / 2
  let E := Real.exp (A * (t - r))
  have htime : ((t - r).toNNReal : ℝ) = t - r := Real.coe_toNNReal _ (sub_nonneg.mpr hrt)
  have hE : Real.exp (((endpointDriftSign ν : ℂ) * ζ).im ^ 2 *
      ((t - r).toNNReal : ℝ) * homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2) =
      E := by rw [htime]; congr 1; dsimp only [A]; ring
  rw [hE]
  have hCb (k : ℕ) : E * C k ≤ Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * t) *
      (t / 2) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + b⁻¹) ^ L k := by
    exact c3Bootstrap_flux_majorant A (growth * ‖ζ‖ ^ 2) (Cder k) K b t r s ε
      (-(d : ℝ) / 4 - (k : ℝ) / 2) (L k)
      (c3Bootstrap_gaussian_rate_le Q ⟨0, by omega⟩ ν ζ growth hrate)
      (mul_nonneg hgrowth (sq_nonneg _)) (hCder k) hK hb ht hr hrt hbs hε
  have hrpos : 0 < r := (half_pos ht).trans_le hr
  have hCder0 := hCder 0
  have hC0 : 0 ≤ C 0 := by dsimp only [C]; positivity
  have hsource := c3Bootstrap_source_norm_le ν ζ
  calc
    _ ≤ E * ((1 / 2 : ℝ) * d * C 1 + ‖ζ‖ * C 0) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsource hC0)) (Real.exp_pos _).le
    _ = ((d : ℝ) / 2) * (E * C 1) + ‖ζ‖ * (E * C 0) := by ring
    _ ≤ ((d : ℝ) / 2) * (Cder 1 * K * Real.exp (growth * ‖ζ‖ ^ 2 * t) *
          (t / 2) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (1 : ℕ) / 2) * (1 + b⁻¹) ^ L 1) +
        ‖ζ‖ * (Cder 0 * K * Real.exp (growth * ‖ζ‖ ^ 2 * t) *
          (t / 2) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (0 : ℕ) / 2) * (1 + b⁻¹) ^ L 0) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hCb 1) (by positivity))
        (mul_le_mul_of_nonneg_left (hCb 0) (norm_nonneg _))
    _ = _ := by
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero]
      ring

/-- The earlier averaged amplitude passes through homogeneous evolution
with coefficient one after enlarging only the exponential growth rate. -/
theorem c3Bootstrap_homogeneous_weight (A g t K w : ℝ)
    (hAg : A ≤ g) (ht : 0 ≤ t) (hK : 0 ≤ K) (hw : 0 ≤ w) :
    Real.exp (A * (t / 2)) * (K * Real.exp (g * (t / 2)) * w) ≤
      K * Real.exp (g * t) * w := by
  have he : Real.exp (A * (t / 2)) * Real.exp (g * (t / 2)) ≤ Real.exp (g * t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hAg) ht]
  calc
    _ = K * (Real.exp (A * (t / 2)) * Real.exp (g * (t / 2))) * w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) hw

/-- The last-half-interval error has the exact bootstrap gain. Neither the
force nor the unrestricted smoothing scale enters the resulting constant. -/
theorem c3Bootstrap_half_error_le (t T ε K E A₀ A₁ X Y m : ℝ)
    (hT : 0 < T) (hTt : T ≤ t) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hm : 0 ≤ m) :
    (t / 2) * (E * (t / 2) ^ (-1 - ε) * K * (A₁ * X + m * A₀ * Y)) ≤
      (2 ^ ε * (A₁ + A₀)) * T ^ (-ε) * K * E * (X + m * Y) := by
  have ht := hT.trans_le hTt
  have hpow := c3Bootstrap_half_integral t ε 1 ht
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hpow
  have hhalf : t - t / 2 = t / 2 := by ring
  rw [hhalf] at hpow
  have hdec := Real.rpow_le_rpow_of_nonpos hT hTt (neg_nonpos.mpr hε)
  have hw : A₁ * X + m * A₀ * Y ≤ (A₁ + A₀) * (X + m * Y) := by
    nlinarith only [mul_nonneg hA₀ hX, mul_nonneg hA₁ (mul_nonneg hm hY)]
  calc
    _ = 2 ^ ε * t ^ (-ε) * K * E * (A₁ * X + m * A₀ * Y) := by
      rw [← hpow]
      ring
    _ ≤ 2 ^ ε * T ^ (-ε) * K * E * ((A₁ + A₀) * (X + m * Y)) := by
      apply mul_le_mul _ hw (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdec (by positivity)) hK) hE
    _ = _ := by ring

end EinsteinFull
