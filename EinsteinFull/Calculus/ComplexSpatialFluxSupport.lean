import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import EinsteinRelation.Entropy.DivergenceSecondAssertion

/-!
# Spatial realization of the zero-force weak flux

Measurable stationary weak divergences transfer to each fixed smooth compact
spatial test, retaining the inhomogeneous source. Real and imaginary projections
reduce to the blueprint's proved real mollifier identity; local L2 realization
justifies every complex spatial pairing.

The actual integrated semigroup flux supplies this weak divergence at zero
force. Its spatial coefficient is the original anisotropic field at x. The
result is almost everywhere for each fixed time and test; a common event for
all tests and samplewise time-integral interchange are separate obligations.
-/

open MeasureTheory Filter
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors

private theorem projection_mul_real (L : ℂ →L[ℝ] ℝ) (z : ℂ) (r : ℝ) :
    L (z * (r : ℂ)) = L z * r := by
  simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using L.map_smul r z

/-- Real scalar projections preserve the actual stationary weak divergence. -/
theorem hasWeakHorizontalDivergence_scalarProjection {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : Fin d → FieldPair d → ℂ) (h : FieldPair d → ℂ)
    (hF : ∀ j, MemLp (F j) 2 Q) (hh : MemLp h 2 Q)
    (hw : ∀ (v : Lp ℂ 2 Q) (V : Fin d → Lp ℂ 2 Q),
      HasComplexHorizontalGradient Q hQ v V →
      (∫ ω, ∑ j, F j ω * V j ω ∂Q) = -(∫ ω, h ω * v ω ∂Q))
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakHorizontalDivergence Q hQ (fun ω j => L (F j ω)) (fun ω => L (h ω)) := by
  refine ⟨fun j => (L.comp_memLp' (hF j)).integrable (by norm_num),
    (L.comp_memLp' hh).integrable (by norm_num), ?_⟩
  intro v _ V hV
  let C := Complex.ofRealCLM.compLpL 2 Q
  have hp := hw (C v) (fun j => C (V j)) (fun j => hasComplexHorizontalDerivative_ofReal (hV j))
  have hi : Integrable (fun ω => ∑ j, F j ω * (C (V j)) ω) Q :=
    integrable_finset_sum _ fun j _ => (hF j).integrable_mul (Lp.memLp (C (V j)))
  have hj : Integrable (fun ω => h ω * C v ω) Q := hh.integrable_mul (Lp.memLp (C v))
  have hp' := congrArg L hp
  rw [← L.integral_comp_comm hi, map_neg, ← L.integral_comp_comm hj] at hp'
  convert hp' using 1
  · apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr fun j => Complex.ofRealCLM.coeFn_compLpL (V j)] with ω hω
    simp only [C, hω, Complex.ofRealCLM_apply, map_sum, projection_mul_real]
  · congr 1
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL v] with ω hω
    simp only [C, hω, Complex.ofRealCLM_apply, projection_mul_real]

/-- A real inhomogeneous horizontal divergence has its literal orbit identity
for each fixed smooth compact spatial test. -/
theorem ae_real_spatial_divergence_fixedTest {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (h : FieldPair d → ℝ)
    (hFm : Measurable F) (hFi : ∀ j, Integrable (fun ω => F ω j) Q)
    (hhm : Measurable h) (hhi : Integrable h Q)
    (hdiv : HasWeakHorizontalDivergence Q hQ F h)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂Q, (∫ x, φ x * h (translate x ω)) =
      -∑ j, ∫ x, coordinateDerivative j φ x * F (translate x ω) j := by
  have he := Entropy.ae_horizontalMollify_eq_of_hasWeakHorizontalDivergence hQ
    hφ hφc hFm hFi hhm hhi hdiv
  have hk (j : Fin d) : Entropy.divKernel φ j = fun x => -coordinateDerivative j φ x := by
    funext x
    -- Chain rule as in the blueprint's coordinateDerivative_reflectKernel.
    have hd : HasFDerivAt (fun y : Vec d => φ (-y))
        ((fderiv ℝ φ x).comp (-ContinuousLinearMap.id ℝ (Vec d))) (-x) := by
      simpa only [neg_neg, Function.comp_def] using!
        ((hφ.differentiable (by simp)) (-(-x))).hasFDerivAt.comp (-x)
          (hasFDerivAt_id (-x)).neg
    change fderiv ℝ (fun y : Vec d => φ (-y)) (-x) (unitVector j) =
      -fderiv ℝ φ x (unitVector j)
    rw [hd.fderiv]
    simp
  simpa only [horizontalMollify, hk, neg_mul, integral_neg, Finset.sum_neg_distrib] using! he

/-- Measurable environment representatives equal almost everywhere agree on
almost every spatial orbit. -/
theorem ae_complex_spatial_orbit_congr {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f g : FieldPair d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[Q] g) :
    ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate x ω) = g (translate x ω) := by
  apply (Measure.ae_ae_comm ?_).mp
    (ae_of_all _ fun x => (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hfg)
  exact measurableSet_eq_fun (hf.comp Probability.continuous_translate.measurable)
    (hg.comp Probability.continuous_translate.measurable)

/-- Literal measurable complex L2 fields are locally L2 on almost every orbit. -/
theorem ae_complex_function_orbit_memLp_on_all_compacts {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : FieldPair d → ℂ} (hfm : Measurable f) (hf : MemLp f 2 Q) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) := by
  filter_upwards [ae_complex_orbit_memLp_on_all_compacts Q hQ (hf.toLp f),
    ae_complex_spatial_orbit_congr Q hQ (Lp.stronglyMeasurable (hf.toLp f)).measurable
      hfm hf.coeFn_toLp] with ω hω he
  exact fun K hK => (hω K hK).ae_eq
    (he.filter_mono (ae_mono Measure.restrict_le_self))

/-- Locally square integrable complex fields can be paired with compact
continuous spatial tests. -/
theorem integrable_spatial_mul_test {d : ℕ} {u : Vec d → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => u x * (φ x : ℂ)) volume := by
  have hl : LocallyIntegrable u volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (hu K hK).integrable (by norm_num)
  simpa only [Complex.real_smul, mul_comm] using
    hl.integrable_smul_left_of_hasCompactSupport hφ hφc

/-- The actual complex horizontal weak divergence transfers to each fixed
smooth compact spatial test, with its nonzero source retained. -/
theorem ae_complex_spatial_divergence_fixedTest {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : Fin d → FieldPair d → ℂ) (h : FieldPair d → ℂ)
    (hFm : ∀ j, Measurable (F j)) (hhm : Measurable h)
    (hF : ∀ j, MemLp (F j) 2 Q) (hh : MemLp h 2 Q)
    (hw : ∀ (v : Lp ℂ 2 Q) (V : Fin d → Lp ℂ 2 Q),
      HasComplexHorizontalGradient Q hQ v V →
      (∫ ω, ∑ j, F j ω * V j ω ∂Q) = -(∫ ω, h ω * v ω ∂Q))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂Q, (∫ x, h (translate x ω) * (φ x : ℂ)) =
      -(∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
  have he (L : ℂ →L[ℝ] ℝ) := ae_real_spatial_divergence_fixedTest Q hQ
    (fun ω j => L (F j ω)) (fun ω => L (h ω))
    (Measurable.of_eval fun j => L.continuous.measurable.comp (hFm j))
    (fun j => (L.comp_memLp' (hF j)).integrable (by norm_num))
    (L.continuous.measurable.comp hhm) ((L.comp_memLp' hh).integrable (by norm_num))
    (hasWeakHorizontalDivergence_scalarProjection Q hQ F h hF hh hw L) φ hφ hφc
  filter_upwards [he Complex.reCLM, he Complex.imCLM,
    ae_complex_function_orbit_memLp_on_all_compacts Q hQ hhm hh,
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      (hFm j) (hF j)] with ω hre him hhω hFω
  have hi := integrable_spatial_mul_test hhω hφ.continuous hφc
  have hj (j : Fin d) : Integrable
      (fun x => F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) volume :=
    integrable_spatial_mul_test (hFω j)
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ (unitVector j))
  have hs := integrable_finset_sum Finset.univ (fun j _ => hj j)
  have hid (L : ℂ →L[ℝ] ℝ)
      (ht : (∫ x, φ x * L (h (translate x ω))) =
        -∑ j, ∫ x, coordinateDerivative j φ x * L (F j (translate x ω))) :
      L (∫ x, h (translate x ω) * (φ x : ℂ)) =
        -L (∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
    rw [← L.integral_comp_comm hi, ← L.integral_comp_comm hs]
    simp_rw [map_sum, projection_mul_real]
    rw [integral_finset_sum _ (fun j _ => by
      simpa only [projection_mul_real] using L.integrable_comp (hj j))]
    simpa only [mul_comm] using ht
  exact Complex.ext (hid Complex.reCLM hre) (hid Complex.imCLM him)

/-- The zero-force cancellation has its actual samplewise spatial flux for
each fixed compact test, at every nonnegative time including zero. -/
theorem IsComplexEnvironmentSemigroup.unforced_orbit_spatial_flux_fixedTest
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {i : Fin d} {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (t : ℝ≥0) (j : Fin d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, P t (β j) (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * ∫ x, ∑ a,
          ((ω.1 x a j : ℂ) + (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∑ b,
            complexCoefficientMul Q a b (hP.gradientOrbit (β j) s b) :
              Lp ℂ 2 (reducedLaw Q)) (translate x ω)) *
            (coordinateDerivative a φ x : ℂ) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Fin d → FieldPair d → ℂ := fun a ω => (ω.1 0 a j : ℂ) +
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∑ b,
      complexCoefficientMul Q a b (hP.gradientOrbit (β j) s b) : Lp ℂ 2 (reducedLaw Q)) ω
  have hF (a : Fin d) : MemLp (F a) 2 (reducedLaw Q) :=
    ((memLp_reduced_coefficient_complex Q a j).mono_exponent le_top).add (Lp.memLp _)
  have hFm (a : Fin d) : Measurable (F a) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem a j)).measurable.add
        (Lp.stronglyMeasurable _).measurable
  have hw (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
      (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
      (∫ ω, ∑ a, F a ω * V a ω ∂reducedLaw Q) =
        -(∫ ω, (2 : ℂ) * P t (β j) ω * v ω ∂reducedLaw Q) := by
    have he := hP.unforced_orbit_weak_flux_timeIntegral hβ t j v V hV
    rw [show (fun ω => (2 : ℂ) * P t (β j) ω * v ω) =
      (fun ω => (2 : ℂ) * (P t (β j) ω * v ω)) by funext ω; ring, integral_const_mul]
    change _ = -(2 * _)
    change _ = -(1 / 2 : ℂ) * (∫ ω, ∑ a, F a ω * V a ω ∂reducedLaw Q) at he
    linear_combination 2 * he
  have he := ae_complex_spatial_divergence_fixedTest (reducedLaw Q) (reducedLaw_stationary Q)
    F (fun ω => (2 : ℂ) * P t (β j) ω) hFm
    (measurable_const.mul (Lp.stronglyMeasurable _).measurable) hF
    ((Lp.memLp _).const_mul (2 : ℂ)) hw φ hφ hφc
  filter_upwards [he] with ω hω
  rw [show (fun x => (2 : ℂ) * P t (β j) (translate x ω) * (φ x : ℂ)) =
    (fun x => (2 : ℂ) * (P t (β j) (translate x ω) * (φ x : ℂ))) by funext x; ring,
    integral_const_mul] at hω
  have hFs : (fun x => ∑ a, F a (translate x ω) * (coordinateDerivative a φ x : ℂ)) =
      (fun x => ∑ a,
        ((ω.1 x a j : ℂ) + (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∑ b,
          complexCoefficientMul Q a b (hP.gradientOrbit (β j) s b) :
            Lp ℂ 2 (reducedLaw Q)) (translate x ω)) * (coordinateDerivative a φ x : ℂ)) := by
    simp only [F, translate_matrix, add_zero]
  rw [hFs] at hω
  linear_combination (1 / 2 : ℂ) * hω

/-- The constructed semigroup discharges the full zero-force spatial flux
identity, without a physical PDE premise. -/
theorem forcedComplexEvolution_unforced_spatial_flux_fixedTest
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    (i : Fin d) {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β)
    (t : ℝ≥0) (j : Fin d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, forcedComplexEvolution Q i 0 t (β j) (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * ∫ x, ∑ a,
          ((ω.1 x a j : ℂ) + (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∑ b,
            complexCoefficientMul Q a b
              ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0).gradientOrbit
                (β j) s b) : Lp ℂ 2 (reducedLaw Q)) (translate x ω)) *
            (coordinateDerivative a φ x : ℂ) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0).unforced_orbit_spatial_flux_fixedTest
    hβ t j φ hφ hφc

end EinsteinFull
