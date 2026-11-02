import EinsteinFull.Calculus.ComplexSpatialFluxSupport

/-!
# The actual forced generator and spatial weak time increments

The full horizontal generator graph gives the spatial divergence source
`2g - 2*zeta*(a e_i).G`. All raw fields below are actual coefficient products
with the unique strong horizontal gradient, with measurability and square
integrability proved internally. The shifted resolvent identifies the generator
of every finite-time orbit primitive, so its spatial identity applies to every
L2 datum, including time zero. Events are for each fixed time and compact test.
The primitive gradient remains a genuine L2 Bochner integral; no samplewise
exchange of temporal integration or physical path-law identification is asserted.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private theorem coefficient_measurable (j k : Fin d) :
    Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
  (Complex.continuous_ofReal.comp
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable

/-- Each actual anisotropic coefficient-flux row is square integrable. -/
theorem memLp_complex_coefficient_flux (Q : EnvironmentLaw d Λ₀ r₀)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    MemLp (fun ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω) 2 (reducedLaw Q) := by
  apply memLp_finset_sum
  intro k _
  exact (Lp.memLp (complexCoefficientMul Q j k (G k))).ae_eq
    (complexCoefficientMul_coe Q j k (G k))

/-- The actual full graph supplies the nonzero horizontal divergence source,
including every signed complex force. -/
theorem IsComplexGeneratorPair.horizontal_flux
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, ∑ j, (∑ k, (ω.1 0 j k : ℂ) * G k ω) * V j ω ∂reducedLaw Q) =
      -(∫ ω, ((2 : ℂ) * g ω - 2 * ζ *
        (∑ j, (ω.1 0 j i : ℂ) * G j ω)) * v ω ∂reducedLaw Q) := by
  obtain ⟨H, hH, hw⟩ := hfg
  have he : H = G := hH.unique hG
  subst H
  have hg : Integrable (fun ω => g ω * v ω) (reducedLaw Q) :=
    (Lp.memLp g).integrable_mul (Lp.memLp v)
  have hd : Integrable
      (fun ω => (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω) (reducedLaw Q) := by
    have hi (j : Fin d) : Integrable
        (fun ω => (ω.1 0 j i : ℂ) * G j ω * v ω) (reducedLaw Q) := by
      have hp := ((Lp.memLp (G j)).integrable_mul (Lp.memLp v)).mul_of_top_right
        (memLp_reduced_coefficient_complex Q j i)
      convert hp using 1
      ext ω
      simp only [Pi.mul_apply]
      ring
    simpa only [Finset.sum_mul] using
      integrable_finset_sum Finset.univ (fun j _ => hi j)
  have heq : (fun ω => ((2 : ℂ) * g ω - 2 * ζ *
      (∑ j, (ω.1 0 j i : ℂ) * G j ω)) * v ω) =
      (fun ω => 2 * (g ω * v ω) - (2 * ζ) *
        ((∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω)) := by
    funext ω
    ring
  rw [heq, integral_sub (hg.const_mul 2) (hd.const_mul (2 * ζ)),
    integral_const_mul, integral_const_mul]
  have hwv := hw v V hV
  simp only [Finset.sum_mul] at hwv ⊢
  linear_combination 2 * hwv

/-- A full actual complex generator pair has its literal spatial weak equation
for every fixed smooth compact test. The event may depend on that test. -/
theorem IsComplexGeneratorPair.spatial_flux_fixedTest
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, g (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
            (coordinateDerivative j φ x : ℂ)) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)) := by
  let F : Fin d → FieldPair d → ℂ := fun j ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  let h : FieldPair d → ℂ := fun ω => 2 * g ω - 2 * ζ * b ω
  have hFm (j : Fin d) : Measurable (F j) :=
    Finset.measurable_sum _ fun k _ =>
      (coefficient_measurable j k).mul (Lp.stronglyMeasurable _).measurable
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    (coefficient_measurable j i).mul (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finset_sum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  have hhm : Measurable h :=
    (measurable_const.mul (Lp.stronglyMeasurable g).measurable).sub
      (measurable_const.mul hbm)
  have hh : MemLp h 2 (reducedLaw Q) :=
    ((Lp.memLp g).const_mul 2).sub (hb.const_mul (2 * ζ))
  have he := ae_complex_spatial_divergence_fixedTest (reducedLaw Q) (reducedLaw_stationary Q)
    F h hFm hhm (memLp_complex_coefficient_flux Q G) hh
    (fun v V hV => hfg.horizontal_flux hG v V hV) φ hφ hφc
  filter_upwards [he, ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) hbm hb] with ω he hgω hbω
  have hg := integrable_spatial_mul_test hgω hφ.continuous hφc
  have hd := integrable_spatial_mul_test hbω hφ.continuous hφc
  have heq : (fun x => h (translate x ω) * (φ x : ℂ)) =
      (fun x => 2 * (g (translate x ω) * (φ x : ℂ)) -
        (2 * ζ) * (b (translate x ω) * (φ x : ℂ))) := by
    funext x
    dsimp [h]
    ring
  rw [heq, integral_sub (hg.const_mul 2) (hd.const_mul (2 * ζ)),
    integral_const_mul, integral_const_mul] at he
  have hFt : (fun x => ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) =
      (fun x => ∑ j, (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
        (coordinateDerivative j φ x : ℂ)) := by
    simp only [F, translate_matrix, add_zero]
  have hbt : (fun x => b (translate x ω) * (φ x : ℂ)) =
      (fun x => (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)) := by
    simp only [b, translate_matrix, add_zero]
  rw [hFt, hbt] at he
  linear_combination (1 / 2 : ℂ) * he

variable {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- Every full forced family commutes with the actual shifted resolvent. -/
theorem IsComplexEnvironmentSemigroup.forced_resolvent_apply
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    forcedComplexResolvent Q i ζ s hs (P t f) =
      P t (forcedComplexResolvent Q i ζ s hs f) := by
  apply IsComplexGeneratorPair.forced_resolvent_unique hs
    (forcedComplexResolvent_spec Q i ζ s hs (P t f))
  simpa only [map_sub, map_smul] using
    hP.map_generator (forcedComplexResolvent_spec Q i ζ s hs f) t

/-- For arbitrary L2 data and signed complex force, the orbit primitive lies
in the complete generator graph, with output equal to its actual increment. -/
theorem IsComplexEnvironmentSemigroup.integral_orbit_graph_forced
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IsComplexGeneratorPair Q i ζ
      (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f) (P t f - f) := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := by dsimp [s]; linarith
  let R := forcedComplexResolvent Q i ζ s hs
  have hc (r : ℝ≥0) : R (P r f) = P r (R f) :=
    hP.forced_resolvent_apply s hs r f
  have hfint := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)
  have hRfint := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 (R f)) (t : ℝ)
  have hRint : (∫ r in Icc (0 : ℝ) (t : ℝ), P r.toNNReal (R f)) =
      R (∫ r in Icc (0 : ℝ) (t : ℝ), P r.toNNReal f) := by
    simp_rw [← hc]
    exact R.integral_comp_comm hfint
  have hfg : IsComplexGeneratorPair Q i ζ (R f) ((s : ℂ) • R f - f) :=
    forcedComplexResolvent_spec Q i ζ s hs f
  have hi := hP.integral_generator_orbit hfg t
  simp_rw [map_sub, map_smul] at hi
  have hsm : IntegrableOn (fun r : ℝ => (s : ℂ) • P r.toNNReal (R f))
      (Icc (0 : ℝ) (t : ℝ)) := hRfint.smul (s : ℂ)
  rw [integral_sub hsm hfint, integral_smul, hRint, ← hc] at hi
  apply (isComplexGeneratorPair_iff_forced_resolvent Q i ζ s hs _ _).mpr
  change R ((s : ℂ) • _ - (P t f - f)) = _
  rw [map_sub, map_smul, map_sub, ← hi]
  module

/-- The actual primitive gives a spatial weak time increment for every datum,
including at time zero, without assuming any physical PDE realization. -/
theorem IsComplexEnvironmentSemigroup.integral_orbit_spatial_flux_fixedTest
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, (P t f - f : Lp ℂ 2 (reducedLaw Q)) (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) *
            ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k) (translate x ω)) *
            (coordinateDerivative j φ x : ℂ)) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
          ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) j) (translate x ω)) *
            (φ x : ℂ)) :=
  (hP.integral_orbit_graph_forced f t).spatial_flux_fixedTest
    (hP.integral_orbit_gradient f t) φ hφ hφc

/-- The time increment is also the literal difference of the translated
endpoint representatives; L2 subtraction introduces no representative premise. -/
theorem IsComplexEnvironmentSemigroup.spatial_increment_fixedTest
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, (P t f (translate x ω) - f (translate x ω)) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) *
            ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k) (translate x ω)) *
            (coordinateDerivative j φ x : ℂ)) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
          ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) j) (translate x ω)) *
            (φ x : ℂ)) := by
  have hr := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (P t f - f)).measurable
    ((Lp.stronglyMeasurable (P t f)).measurable.sub (Lp.stronglyMeasurable f).measurable)
    (Lp.coeFn_sub (P t f) f)
  filter_upwards [hP.integral_orbit_spatial_flux_fixedTest f t φ hφ hφc, hr] with ω he hr
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  rw [hx]
  rfl

/-- The constructed forced evolution discharges the full semigroup predicate
in the literal spatial weak time-increment identity. -/
theorem forcedComplexEvolution_integral_spatial_flux_fixedTest
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, (forcedComplexEvolution Q i ζ t f (translate x ω) -
        f (translate x ω)) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) *
            ((∫ s in Icc (0 : ℝ) (t : ℝ),
              (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) k)
                (translate x ω)) * (coordinateDerivative j φ x : ℂ)) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
          ((∫ s in Icc (0 : ℝ) (t : ℝ),
            (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) j)
              (translate x ω)) * (φ x : ℂ)) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).spatial_increment_fixedTest
    f t φ hφ hφc

/-- Generator-domain data satisfy the actual spatial equation along every
positive-time forced orbit, with its genuine time-generator output. -/
theorem IsComplexEnvironmentSemigroup.generator_orbit_spatial_flux_fixedTest
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) (ht : 0 < t)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, P t g (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) * (hP.forcedGradient t ht f k) (translate x ω)) *
            (coordinateDerivative j φ x : ℂ)) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
          (hP.forcedGradient t ht f j) (translate x ω)) * (φ x : ℂ)) :=
  (hP.map_generator hfg t).spatial_flux_fixedTest (hP.forcedGradient_spec t ht f) φ hφ hφc

end EinsteinFull
