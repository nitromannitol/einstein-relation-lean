import EinsteinFull.Calculus.CommonSpatialTestsSupport
import EinsteinFull.Calculus.ComplexPhysicalWeakTimeSupport

/-!
# Common spatial events for the actual signed complex equation

Inhomogeneous weak divergence, the actual generator pair and temporal tests
are realized on one event before every smooth compact spatial test. Joint
representatives are chosen before temporal tests. Temporal tests are fixed
before the event; prescribed countable families can share that event.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Inhomogeneous complex horizontal divergence transfers on one event for
all spatial tests, with the actual nonzero source retained. -/
theorem ae_complex_spatial_divergence_all_tests {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : Fin d → FieldPair d → ℂ) (h : FieldPair d → ℂ)
    (hFm : ∀ j, Measurable (F j)) (hhm : Measurable h)
    (hF : ∀ j, MemLp (F j) 2 Q) (hh : MemLp h 2 Q)
    (hw : ∀ (v : Lp ℂ 2 Q) (V : Fin d → Lp ℂ 2 Q),
      HasComplexHorizontalGradient Q hQ v V →
      (∫ ω, ∑ j, F j ω * V j ω ∂Q) = -(∫ ω, h ω * v ω ∂Q)) :
    ∀ᵐ ω ∂Q, ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, h (translate x ω) * (φ x : ℂ)) =
        -(∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
  have hloc : ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => h (translate x ω)) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => F j (translate x ω)) 2 (volume.restrict K) := by
    filter_upwards [ae_complex_function_orbit_memLp_on_all_compacts Q hQ hhm hh,
      ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
        (hFm j) (hF j)] with ω hhω hFω
    exact fun K hK => ⟨hhω K hK, fun j => hFω j K hK⟩
  have hi (ω : FieldPair d)
      (hω : ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => h (translate x ω)) 2 (volume.restrict K) ∧
          ∀ j, MemLp (fun x => F j (translate x ω)) 2 (volume.restrict K))
      (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
      Integrable (fun x => h (translate x ω) * (φ x : ℂ)) volume ∧
        Integrable (fun x => ∑ j, F j (translate x ω) *
          (coordinateDerivative j φ x : ℂ)) volume := by
    refine ⟨integrable_spatial_mul_test (fun K hK => (hω K hK).1) hφ.continuous hφc,
      integrable_finset_sum _ fun j _ => ?_⟩
    exact integrable_spatial_mul_test (fun K hK => (hω K hK).2 j)
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (unitVector j))
  have he := ae_all_spatial_tests_of_ae_fixed_test Q
    (fun ω x => h (translate x ω)) (fun ω j x => F j (translate x ω)) hloc
    (fun φ hφ hφc => by
      filter_upwards [hloc,
        ae_complex_spatial_divergence_fixedTest Q hQ F h hFm hhm hF hh hw φ hφ hφc]
        with ω hω he
      rw [integral_add (hi ω hω φ hφ hφc).1 (hi ω hω φ hφ hφc).2, he,
        neg_add_cancel])
  filter_upwards [hloc, he] with ω hω he
  intro φ hφ hφc
  have heφ := he φ hφ hφc
  rw [integral_add (hi ω hω φ hφ hφc).1 (hi ω hω φ hφ hφc).2] at heφ
  exact eq_neg_of_add_eq_zero_left heφ

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private theorem complex_coefficient_measurable (j k : Fin d) :
    Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
  (Complex.continuous_ofReal.comp
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable

/-- A full actual generator pair has one spatial weak-equation event before
all smooth compact spatial tests, including its signed complex drift. -/
theorem IsComplexGeneratorPair.spatial_flux_all_tests
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
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
      (complex_coefficient_measurable j k).mul (Lp.stronglyMeasurable _).measurable
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    (complex_coefficient_measurable j i).mul (Lp.stronglyMeasurable _).measurable
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
  have he := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    F h hFm hhm (memLp_complex_coefficient_flux Q G) hh
    (fun v V hV => hfg.horizontal_flux hG v V hV)
  filter_upwards [he, ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) hbm hb] with ω he hgω hbω
  intro φ hφ hφc
  have he := he φ hφ hφc
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

/-- All-data temporal testing, on a common event for all spatial tests at
each fixed C1 temporal weight and horizon. -/
theorem IsComplexEnvironmentSemigroup.time_test_spatial_flux_all_tests
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
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
  filter_upwards [hgraph.spatial_flux_all_tests
    (hP.weighted_integral_orbit_gradient f η hηc t), hr] with ω he hr
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


/-- A single pair of actual joint representatives gives the temporal weak
equation on one event before every spatial test. The temporal test remains
fixed before this event; no temporal trace is inferred. -/
theorem IsComplexEnvironmentSemigroup.exists_joint_weak_time_equation_all_spatial_tests
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 →
        ∀ᵐ ω ∂reducedLaw Q,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
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
  intro η η' hη hη' t hzero ht
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η' hη'
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j) η hηc
  filter_upwards [hP.time_test_spatial_flux_all_tests f η η' hη hη' t hzero ht,
    hcu, ae_all_iff.mpr hcv] with ω he hcu hcv
  intro φ hφ hφc
  have he := he φ hφ hφc
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

/-- The constructed signed-complex evolution supplies all actual semigroup,
graph, gradient and joint-representative producers internally. -/
theorem forcedComplexEvolution_exists_joint_weak_time_equation_all_spatial_tests
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] forcedComplexEvolution Q i ζ s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q]
        ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 →
        ∀ᵐ ω ∂reducedLaw Q,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).exists_joint_weak_time_equation_all_spatial_tests f


/-- One actual joint representative family satisfies every spatial test and
every member of any prescribed countable family of temporal tests, on one
environment event. Countability is explicit. -/
theorem forcedComplexEvolution_exists_joint_countable_weak_time_equations
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] forcedComplexEvolution Q i ζ s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q]
        ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) j) ∧
      ∀ (η η' : ℕ → ℝ → ℝ), (∀ n s, HasDerivAt (η n) (η' n s) s) →
        (∀ n, Continuous (η' n)) → ∀ (t : ℕ → ℝ≥0),
        (∀ n, η n 0 = 0) → (∀ n, η n (t n) = 0) →
        ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (t n : ℝ), (η' n s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t n : ℝ), (η n s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (t n : ℝ), (η n s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) := by
  obtain ⟨U, V, hU, hV, heU, heV, he⟩ :=
    forcedComplexEvolution_exists_joint_weak_time_equation_all_spatial_tests Q i ζ f
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro η η' hη hη' t hzero ht
  exact ae_all_iff.mpr fun n => he (η n) (η' n) (hη n) (hη' n) (t n) (hzero n) (ht n)

end EinsteinFull
