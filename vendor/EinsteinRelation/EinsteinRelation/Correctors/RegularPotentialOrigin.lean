import EinsteinRelation.Correctors.StationaryOriginIdentification
import EinsteinRelation.Correctors.HarmonicRepresentativeNormalization

/-!
# The origin identity for regular corrector potentials

Source: `paper/main.tex:693-698,727-729`. Hölder continuity of the spatial
gradient and stationarity identify its value at zero with the canonical
environment gradient. This identification does not require evaluating a
spatial a.e. equality at zero or choosing a jointly measurable potential.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- The explicit Euclidean Hölder bound gives continuity at every interior point. -/
theorem continuousAt_of_holderBound {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {α K : ℝ} (hα : 0 < α) {f : Vec d → ℝ} (hf : HolderBound U α f K)
    {x : Vec d} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨S, H, -, -, -, -, hH⟩ := hf
  have hc : Continuous (fun y : Vec d => H * euclideanNorm (y - x) ^ α) := by
    apply continuous_const.mul
    apply (Real.continuous_rpow_const hα.le).comp
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hlim : Tendsto (fun y : Vec d => H * euclideanNorm (y - x) ^ α)
      (𝓝 x) (𝓝 0) := by
    simpa only [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, Real.sqrt_zero, Real.zero_rpow hα.ne', mul_zero]
      using hc.tendsto x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hU.mem_nhds hx] with y hy
  simpa only [Real.norm_eq_abs] using hH y hy x hx

private theorem isOpen_unitBall (d : ℕ) : IsOpen (ball (0 : Vec d) 1) := by
  unfold ball euclideanNorm euclideanSq dot
  exact isOpen_lt (by fun_prop) continuous_const

private theorem zero_mem_unitBall (d : ℕ) : (0 : Vec d) ∈ ball 0 1 := by
  simp only [ball, Set.mem_setOf_eq, sub_self, euclideanNorm, euclideanSq, dot,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, Real.sqrt_zero]
  exact zero_lt_one

/-- The continuous gradient of any local regular realization agrees at the
origin almost surely with the selected canonical L² representative. -/
theorem ae_regularPotential_gradient_origin {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      C1Alpha (ball 0 1) (1 / 2) u g →
      (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
        g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x ω)).ofLp) →
      g 0 = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp := by
  have ha : ∀ j : Fin d, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∀ (U : Set (Vec d)), IsOpen U → (0 : Vec d) ∈ U →
        ∀ (f : Vec d → ℝ), ContinuousAt f 0 →
          (∀ᵐ x ∂volume.restrict U,
            (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x ω)) j = f x) →
          f 0 = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω) j := by
    intro j
    apply ae_origin_eq_of_continuous_representative _ (reducedEnvironmentLaw_stationary Q)
      (F := fun ω => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω) j)
    exact measurable_const.add
      ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).continuous.measurable.comp
        (Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable)
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  intro u g hreg hspatial
  ext j
  obtain ⟨K, hK⟩ := hreg.2
  exact hω j _ (isOpen_unitBall d) (zero_mem_unitBall d) (fun x => g x j)
    (continuousAt_of_holderBound (isOpen_unitBall d) (by norm_num : (0 : ℝ) < 1 / 2)
      (hK j) (zero_mem_unitBall d))
    (hspatial.mono fun x hx => congrArg (fun v : Vec d => v j) hx.symm)

/-- The samplewise regular potential only needs the spatial a.e. gradient
identity: its origin identity follows from stationarity. Existence and
regularity of that potential remain separate internal obligations. -/
theorem canonicalHarmonicRealization_of_spatial_regular_potentials
    (hpot : ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ : ℝ)
      (Q : EnvironmentLaw d L r₀) (i : Fin d), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
        (∀ R : ℝ, 0 < R → R ≤ 1 → WeakSolution (ball 0 R) ω.1 u g) ∧
        C1Alpha (ball 0 1) (1 / 2) u g ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
          g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp)) :
    CanonicalHarmonicRealization := by
  apply canonicalHarmonicRealization_of_regular_potentials
  intro d hd L r₀ Q i
  filter_upwards [hpot d hd L r₀ Q i, ae_regularPotential_gradient_origin Q i]
    with ω hω horigin
  obtain ⟨u, g, hweak, hreg, hspatial⟩ := hω
  exact ⟨u, g, hweak, hreg, hspatial, horigin u g hreg hspatial⟩

end EinsteinRelation.Correctors

