import EinsteinFull.Work.W2.TransposeAllDataHorizonEnergySupport
import EinsteinFull.Calculus.ComplexTransposeWeakTimeSupport
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport

/-!
# Time integrals of the actual transpose gradient

The all-L² transpose energy construction supplies an almost everywhere strong
horizontal gradient on every finite horizon. Closedness of each horizontal
derivative graph identifies the gradient of a weighted time primitive with
the integral of these actual gradients. The spatial flux identity therefore
uses this integral, retaining the true transpose's column-gradient drift.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Finite-horizon transpose energy gives Bochner integrability down to time zero. -/
theorem IsComplexTransposeSemigroup.integrableOn_gradientOrbit
    (hT : IsComplexTransposeSemigroup Q P T) (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IntegrableOn (complexTransposeGradientOrbit Q T f) (Icc (0 : ℝ) (t : ℝ)) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (hT.gradientOrbit_horizon_energy hP f t).1

/-- A continuous real time weight preserves integrability of the actual gradient. -/
theorem IsComplexTransposeSemigroup.integrableOn_weighted_gradientOrbit
    (hT : IsComplexTransposeSemigroup Q P T) (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (η : ℝ → ℝ) (hη : Continuous η) (t : ℝ≥0) :
    IntegrableOn (fun s => η s • complexTransposeGradientOrbit Q T f s)
      (Icc (0 : ℝ) (t : ℝ)) :=
  (hT.integrableOn_gradientOrbit hP f t).continuousOn_smul hη.continuousOn isCompact_Icc

/-- The weighted primitive has the integral of the actual all-data gradient,
without a domain or initial H¹ assumption on the datum. -/
theorem IsComplexTransposeSemigroup.weighted_integral_orbit_gradient
    (hT : IsComplexTransposeSemigroup Q P T) (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (η : ℝ → ℝ) (hη : Continuous η) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f)
      (fun k => (∫ s in Icc (0 : ℝ) (t : ℝ),
        η s • complexTransposeGradientOrbit Q T f s) k) := by
  intro k
  let E := PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))
  let C : E →L[ℂ] Lp ℂ 2 (reducedLaw Q) := PiLp.proj 2 _ k
  have hc : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hf := (hη.smul hc).continuousOn.integrableOn_Icc
    (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))
  have hg := hT.integrableOn_weighted_gradientOrbit hP f η hη t
  have hkg := C.integrable_comp hg
  have ha := (hT.gradientOrbit_horizon_energy hP f t).2.1
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at ha
  have hd : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) k
        (η s • T s.toNNReal f) (C (η s • complexTransposeGradientOrbit Q T f s)) := by
    filter_upwards [ha] with s hs
    simpa only [C, ContinuousLinearMap.map_smul_of_tower, Complex.coe_smul]
      using! (hs k).smul (η s : ℂ)
  have hi := HasComplexHorizontalDerivative.integral_of_ae hf hkg hd
  rw [C.integral_comp_comm hg] at hi
  exact hi

/-- On one event before all spatial tests, the time-tested true-transpose flux
uses the integral of its actual all-L² gradients. The time test and horizon
are fixed before that event. -/
theorem IsComplexTransposeSemigroup.time_test_spatial_flux_integrated_gradient
    (hT : IsComplexTransposeSemigroup Q P T) (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (η η' : ℝ → ℝ)
    (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), η' s • T s.toNNReal f)
          (translate x ω) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) *
              ((∫ s in Icc (0 : ℝ) (t : ℝ),
                η s • complexTransposeGradientOrbit Q T f s) k) (translate x ω)) -
              2 * ζ * (ω.1 x j i : ℂ) *
                (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f) (translate x ω)) *
                  (coordinateDerivative j φ x : ℂ)) := by
  obtain ⟨G, hG, he⟩ :=
    hT.time_test_spatial_flux_all_tests hP f η η' hη hη' t hzero ht
  have hc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hgrad := hT.weighted_integral_orbit_gradient hP f η hc t
  have hsame := hG.unique hgrad
  simpa only [hsame] using he

end EinsteinFull
