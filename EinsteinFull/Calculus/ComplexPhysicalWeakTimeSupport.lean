import EinsteinFull.Calculus.ComplexGeneratorSpatialSupport
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof

/-!
# Temporal tests for the actual complex evolution

Continuous temporal weights preserve the actual strong horizontal gradient
under integration. Temporal integration by parts in the complete generator
graph then gives a spatial weak equation for arbitrary L2 initial data. Joint
measurable representatives turn every integral in that equation into a literal
samplewise time integral. The environment event is for each fixed pair of
temporal and spatial tests; no common event for all tests is asserted here.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- A continuous temporal weight commutes with the actual strong gradient,
including the integrable positive-time gradient singularity at zero. -/
theorem IsComplexEnvironmentSemigroup.weighted_integral_orbit_gradient
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (η : ℝ → ℝ) (hη : Continuous η) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • P s.toNNReal f)
      (fun k => ∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) k) := by
  intro k
  let T := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k
  have hf := (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)).continuousOn_smul
    hη.continuousOn isCompact_Icc
  have hkg : IntegrableOn (fun s => (hP.gradientOrbit f s) k) (Icc (0 : ℝ) (t : ℝ)) :=
    T.integrable_comp (hP.integrableOn_gradientOrbit f t)
  have hg := hkg.continuousOn_smul hη.continuousOn isCompact_Icc
  apply HasComplexHorizontalDerivative.integral_of_ae hf hg
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
  simpa only [Complex.coe_smul] using!
    (hP.gradientOrbit_spec f (lt_of_le_of_ne hs.1 (Ne.symm hs0)) k).smul (η s : ℂ)

/-- Distributional temporal testing in the actual full generator graph,
followed by its fixed-spatial-test equation. The temporal derivative appears
with the sign dictated by integration by parts. -/
theorem IsComplexEnvironmentSemigroup.timeTest_spatial_flux_fixedTest
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), η' s • P s.toNNReal f)
        (translate x ω) * (φ x : ℂ)) =
        (1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) *
            (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) k)
              (translate x ω)) * (coordinateDerivative j φ x : ℂ)) -
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) j)
            (translate x ω)) * (φ x : ℂ)) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hgraph := hP.generator_timeTest_allData f η η' hη hη' t hzero ht
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hgraph
  let g : Lp ℂ 2 (reducedLaw Q) := ∫ s in Icc (0 : ℝ) (t : ℝ), η' s • P s.toNNReal f
  have hr := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (-g)).measurable (Lp.stronglyMeasurable g).measurable.neg
    (Lp.coeFn_neg g)
  filter_upwards [hgraph.spatial_flux_fixedTest
    (hP.weighted_integral_orbit_gradient f η hηc t) φ hφ hφc, hr] with ω he hr
  have hn : (∫ x, (-g) (translate x ω) * (φ x : ℂ)) =
      -(∫ x, g (translate x ω) * (φ x : ℂ)) := by
    calc
      _ = ∫ x, -(g (translate x ω) * (φ x : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [hr] with x hx
        rw [hx]
        simp only [Pi.neg_apply, neg_mul]
      _ = _ := integral_neg _
  change (∫ x, (-g) (translate x ω) * (φ x : ℂ)) = _ at he
  rw [hn] at he
  change (∫ x, g (translate x ω) * (φ x : ℂ)) = _
  linear_combination -he

/-- A continuous real temporal weight can be passed to a literal joint
representative before spatial translation. -/
theorem ae_spatial_weighted_integral_joint_l2_representative
    {u : ℝ → Lp ℂ 2 (reducedLaw Q)} {U : ℝ × FieldPair d → ℂ}
    (t : ℝ≥0) (hu : IntegrableOn u (Icc (0 : ℝ) (t : ℝ)))
    (hU : Measurable U) (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (η : ℝ → ℝ) (hη : Continuous η) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • u s) (translate x ω) =
        ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω) := by
  apply ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q)
    (hu.continuousOn_smul hη.continuousOn isCompact_Icc)
    ((Complex.measurable_ofReal.comp (hη.measurable.comp measurable_fst)).fun_mul hU)
  intro s
  filter_upwards [heU s, Lp.coeFn_smul (η s) (u s)] with ω hω hs
  simp only [Pi.smul_apply, Function.comp_def] at hs ⊢
  rw [hs, hω]
  rfl

/-- One pair of jointly measurable actual orbit/gradient representatives
satisfies each separated temporal/spatial weak test. The representatives are
chosen before the tests; the null event may depend on those tests. -/
theorem IsComplexEnvironmentSemigroup.exists_joint_weak_time_equation
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 →
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) := by
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative f
  obtain ⟨V, hV, heV⟩ := hP.exists_joint_gradient_representative f
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro η η' hη hη' t hzero ht φ hφ hφc
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η' hη'
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j) η hηc
  filter_upwards [hP.timeTest_spatial_flux_fixedTest f η η' hη hη' t hzero ht φ hφ hφc,
    hcu, ae_all_iff.mpr hcv] with ω he hcu hcv
  have hgc : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j,
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) j) (translate x ω) =
        ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω) :=
    ae_all_iff.mpr hcv
  have hleft := integral_congr_ae (hcu.mono fun x hx => congrArg (· * (φ x : ℂ)) hx)
  have hprincipal : (∫ x, ∑ j, (∑ k, (ω.1 x j k : ℂ) *
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) k) (translate x ω)) *
      (coordinateDerivative j φ x : ℂ)) =
      ∫ x, ∑ j, (∑ k, (ω.1 x j k : ℂ) *
        (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
        (coordinateDerivative j φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hgc] with x hx
    simp_rw [hx]
  have hdrift : (∫ x, (∑ j, (ω.1 x j i : ℂ) *
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) j) (translate x ω)) *
      (φ x : ℂ)) =
      ∫ x, (∑ j, (ω.1 x j i : ℂ) *
        (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
        (φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hgc] with x hx
    simp_rw [hx]
  rwa [hleft, hprincipal, hdrift] at he

/-- The constructed forced evolution supplies the full semigroup predicate
internally in the joint-representative weak-time equation. -/
theorem forcedComplexEvolution_exists_joint_weak_time_equation
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] forcedComplexEvolution Q i ζ s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q]
        ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 →
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).exists_joint_weak_time_equation f

end EinsteinFull
