import EinsteinFull.Calculus.ComplexTransposeSpatialSupport
import EinsteinFull.Calculus.ComplexPhysicalWeakTimeSupport

/-!
# Weak-time testing of the actual bilinear transpose

Forward orbit differentiation and the actual bilinear transpose identity give
its weighted time primitive in the full transpose generator graph. The reverse
adjoint-graph theorem constructs its H1 gradient internally. The spatial weak
equation keeps that actual primitive gradient; it does not identify it with a
time integral of an as yet unconstructed transpose gradient orbit.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private def pairCLM (f : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 f

private theorem pairCLM_apply (f g : Lp ℂ 2 (reducedLaw Q)) :
    pairCLM f g = ∫ ω, g ω * f ω ∂reducedLaw Q := by
  rw [pairCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => mul_comm _ _

/-- For arbitrary L2 data the actual transpose weighted orbit has a full H1
transpose generator pair, without any transpose-domain or gradient premise. -/
theorem IsComplexTransposeSemigroup.generator_timeTest_allData
    (hT : IsComplexTransposeSemigroup Q P T) (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (η η' : ℝ → ℝ)
    (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    IsComplexTransposeGeneratorPair Q i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), η s • T s.toNNReal f)
      (-(∫ s in (0 : ℝ)..(t : ℝ), η' s • T s.toNNReal f)) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hcT : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hb (s : ℝ) (u : Lp ℂ 2 (reducedLaw Q)) :
      pairCLM u (T s.toNNReal f) = pairCLM f (P s.toNNReal u) := by
    simp only [pairCLM_apply]
    simpa only [mul_comm] using (hT s.toNNReal u f).symm
  apply (isComplexTransposeGeneratorPair_iff_bilinear_adjoint Q i ζ _ _).mpr
  intro u v huv
  have hu : Continuous (fun s : ℝ => pairCLM f (P s.toNNReal u)) :=
    (pairCLM f).continuous.comp ((hP.2.2.1 u).comp continuous_real_toNNReal)
  have hv : Continuous (fun s : ℝ => pairCLM f (P s.toNNReal v)) :=
    (pairCLM f).continuous.comp ((hP.2.2.1 v).comp continuous_real_toNNReal)
  have hd (s : ℝ) (hs : 0 ≤ s) :
      HasDerivWithinAt (fun r : ℝ => pairCLM f (P r.toNNReal u))
        (pairCLM f (P s.toNNReal v)) (Ici s) s :=
    ((pairCLM f).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s
      (hP.hasDerivWithinAt_orbit huv s hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (NNReal.coe_nonneg t)
    (hηc.fun_smul hu).continuousOn
    (f' := fun s => η' s • pairCLM f (P s.toNNReal u) +
      η s • pairCLM f (P s.toNNReal v))
    (fun s hs => by
      simpa only [add_comm] using! ((hη s).hasDerivWithinAt.smul (hd s hs.1.le)).mono
        Ioi_subset_Ici_self)
    (((hη'.fun_smul hu).add (hηc.fun_smul hv)).intervalIntegrable 0 t)
  simp only [ht, hzero, zero_smul, sub_self] at he
  rw [intervalIntegral.integral_add ((hη'.fun_smul hu).intervalIntegrable (μ := volume) 0 t)
    ((hηc.fun_smul hv).intervalIntegrable (μ := volume) 0 t)] at he
  rw [← pairCLM_apply u, ← pairCLM_apply v, map_neg,
    ← (pairCLM u).intervalIntegral_comp_comm ((hη'.fun_smul hcT).intervalIntegrable 0 t),
    ← (pairCLM v).intervalIntegral_comp_comm ((hηc.fun_smul hcT).intervalIntegrable 0 t)]
  have hbu (s : ℝ) : pairCLM u (η' s • T s.toNNReal f) =
      η' s • pairCLM f (P s.toNNReal u) := by
    rw [(pairCLM u).map_smul_of_tower, hb]
  have hbv (s : ℝ) : pairCLM v (η s • T s.toNNReal f) =
      η s • pairCLM f (P s.toNNReal v) := by
    rw [(pairCLM v).map_smul_of_tower, hb]
  simp_rw [hbu, hbv]
  exact neg_eq_of_add_eq_zero_right he

/-- Temporal testing of the actual transpose gives a conservative spatial
flux equation on one event for all spatial tests at each fixed time test.
The gradient belongs to the actual weighted L2 primitive. -/
theorem IsComplexTransposeSemigroup.time_test_spatial_flux_all_tests
    (hT : IsComplexTransposeSemigroup Q P T) (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (η η' : ℝ → ℝ)
    (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f) G ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), η' s • T s.toNNReal f)
            (translate x ω) * (φ x : ℂ)) =
            (1 / 2 : ℂ) * (∫ x, ∑ j,
              ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
                2 * ζ * (ω.1 x j i : ℂ) *
                  (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f) (translate x ω)) *
                    (coordinateDerivative j φ x : ℂ)) := by
  have hg := hT.generator_timeTest_allData hP f η η' hη hη' t hzero ht
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hg
  obtain ⟨G, hG, he⟩ := hg.exists_spatial_flux_all_tests
  refine ⟨G, hG, ?_⟩
  let g : Lp ℂ 2 (reducedLaw Q) := ∫ s in Icc (0 : ℝ) (t : ℝ), η' s • T s.toNNReal f
  have hr := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (-g)).measurable (Lp.stronglyMeasurable g).measurable.neg
    (Lp.coeFn_neg g)
  filter_upwards [he, hr] with ω he hr
  intro φ hφ hφc
  have he := he φ hφ hφc
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

/-- The constructed evolution and its actual bilinear transpose supply the
full time-tested transpose graph internally for every L2 datum. -/
theorem complexL2Transpose_forcedComplexEvolution_generator_timeTest
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    IsComplexTransposeGeneratorPair Q i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), η s •
        complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i ζ s.toNNReal) f)
      (-(∫ s in (0 : ℝ)..(t : ℝ), η' s •
        complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i ζ s.toNNReal) f)) :=
  (isComplexTransposeSemigroup_complexL2Transpose Q (forcedComplexEvolution Q i ζ)).generator_timeTest_allData
    (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ) f η η' hη hη' t hzero ht

end EinsteinFull
