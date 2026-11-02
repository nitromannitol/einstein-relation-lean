import EinsteinFull.Calculus.CommonTemporalTestsSupport
import EinsteinFull.Calculus.ComplexCommonSpatialSupport

/-!
# Common temporal and spatial weak-equation events

The actual joint representatives have local space-time L1 on every compact
spatial set and integer time window. Their weak functional is continuous in
the uniform temporal value/derivative jet. Dense countable jets therefore
remove temporal-test exceptional sets, while keeping every spatial test.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation CommonTemporalTests

private abbrev TimeWindow (n : ℕ) := Icc (0 : ℝ) (n : ℝ)
private abbrev TimeJet (n : ℕ) := C(TimeWindow n, ℝ) × C(TimeWindow n, ℝ)
private def clampTime (n : ℕ) : ℝ → TimeWindow n := projIcc (0 : ℝ) (n : ℝ) (by positivity)
private theorem measurable_clampTime (n : ℕ) : Measurable (clampTime n) :=
  continuous_projIcc.measurable
private def restrictTime (n : ℕ) (η : ℝ → ℝ) (hc : Continuous η) : C(TimeWindow n, ℝ) :=
  ⟨fun s => η s, hc.comp continuous_subtype_val⟩
private def c1Jets (n : ℕ) : Set (TimeJet n) :=
  {q | ∃ (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η'),
    η 0 = 0 ∧ η n = 0 ∧ q =
      (restrictTime n η (continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt),
        restrictTime n η' hη')}
private def timeWeight {n : ℕ} (w : C(TimeWindow n, ℝ)) (s : ℝ) : ℝ := w (clampTime n s)
private theorem measurable_timeWeight {n : ℕ} (w : C(TimeWindow n, ℝ)) :
    Measurable (timeWeight w) := w.continuous.measurable.comp (measurable_clampTime n)
private theorem timeWeight_bound {n : ℕ} (w : C(TimeWindow n, ℝ)) (s : ℝ) :
    ‖timeWeight w s‖ ≤ ‖w‖ := w.norm_coe_le_norm _
private theorem integral_restrictTime {n : ℕ} (η : ℝ → ℝ) (hc : Continuous η)
    (F : ℝ → ℂ) :
    (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight (restrictTime n η hc) s : ℂ) * F s) =
      ∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * F s := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only [timeWeight, restrictTime, ContinuousMap.coe_mk, clampTime, projIcc_of_mem (by positivity : (0 : ℝ) ≤ n) hs]

private def weakTimeFunctional {d : ℕ} (i : Fin d) (ζ : ℂ) (n : ℕ)
    (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ)
    (ω : FieldPair d) (φ : Vec d → ℝ) (q : TimeJet n) : ℂ :=
  (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.2 s : ℂ) *
      U (s, translate x ω)) * (φ x : ℂ)) -
    (1 / 2 : ℂ) * (∫ x, ∑ j,
      (∑ k, (ω.1 x j k : ℂ) *
        (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) * V k (s, translate x ω))) *
        (coordinateDerivative j φ x : ℂ)) +
    ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
      (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) * V j (s, translate x ω))) *
        (φ x : ℂ))

private theorem continuous_principal_time_pairing {d : ℕ} (n : ℕ)
    (V : Fin d → ℝ × FieldPair d → ℂ) (ω : FieldPair d)
    (hV : ∀ k K, IsCompact K → Integrable
      (fun p : Vec d × ℝ => V k (p.2, translate p.1 ω))
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Continuous (fun q : TimeJet n => ∫ x, ∑ j,
      (∑ k, (ω.1 x j k : ℂ) *
        (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) * V k (s, translate x ω))) *
          (coordinateDerivative j φ x : ℂ)) := by
  let a : Fin d → Fin d → Vec d → ℂ := fun j k x => (ω.1 x j k : ℂ)
  have ha (j k : Fin d) : Continuous (a j k) :=
    Complex.continuous_ofReal.comp (ω.1.continuous.matrix_elem j k)
  have hdc (j : Fin d) : Continuous (fun x => (coordinateDerivative j φ x : ℂ)) :=
    Complex.continuous_ofReal.comp ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hds (j : Fin d) : HasCompactSupport (fun x => (coordinateDerivative j φ x : ℂ)) :=
    (hφc.fderiv_apply ℝ (unitVector j)).comp_left (g := Complex.ofReal) rfl
  have hc : Continuous (fun q : TimeJet n => ∑ j, ∑ k,
      ∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) *
        V k (s, translate x ω)) * (a j k x * (coordinateDerivative j φ x : ℂ))) := by
    apply continuous_finset_sum
    intro j _
    apply continuous_finset_sum
    intro k _
    exact (continuous_spatial_temporal_pairing (hV k) ((ha j k).mul (hdc j))
      ((hds j).mul_left (f := a j k)) (measurable_clampTime n)).comp continuous_fst
  exact hc.congr fun q => (integral_matrix_pairing hV a ha
    (fun j x => (coordinateDerivative j φ x : ℂ)) hdc hds
    (measurable_timeWeight q.1) (timeWeight_bound q.1)).symm

private theorem continuous_drift_time_pairing {d : ℕ} (i : Fin d) (n : ℕ)
    (V : Fin d → ℝ × FieldPair d → ℂ) (ω : FieldPair d)
    (hV : ∀ k K, IsCompact K → Integrable
      (fun p : Vec d × ℝ => V k (p.2, translate p.1 ω))
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (fun q : TimeJet n => ∫ x,
      (∑ j, (ω.1 x j i : ℂ) *
        (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) * V j (s, translate x ω))) *
        (φ x : ℂ)) := by
  let a : Fin d → Fin d → Vec d → ℂ := fun j k x => (ω.1 x j k : ℂ)
  have ha (j k : Fin d) : Continuous (a j k) :=
    Complex.continuous_ofReal.comp (ω.1.continuous.matrix_elem j k)
  have hφr : Continuous (fun x => (φ x : ℂ)) := Complex.continuous_ofReal.comp hφ
  have hφrc : HasCompactSupport (fun x => (φ x : ℂ)) := hφc.comp_left (g := Complex.ofReal) rfl
  have hc : Continuous (fun q : TimeJet n => ∑ j, ∫ x,
      (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) * V j (s, translate x ω)) *
        (a j i x * (φ x : ℂ))) := by
    apply continuous_finset_sum
    intro j _
    exact (continuous_spatial_temporal_pairing (hV j) ((ha j i).mul hφr)
      (hφrc.mul_left (f := a j i)) (measurable_clampTime n)).comp continuous_fst
  apply hc.congr
  intro q
  have hi (j : Fin d) := (spatial_temporal_pairing (hV j) ((ha j i).mul hφr)
    (hφrc.mul_left (f := a j i)) (measurable_timeWeight q.1) (timeWeight_bound q.1)).1
  symm
  simp_rw [Finset.sum_mul]
  calc
    _ = ∫ x, ∑ j, (∫ s in Icc (0 : ℝ) (n : ℝ), (timeWeight q.1 s : ℂ) *
        V j (s, translate x ω)) * (a j i x * (φ x : ℂ)) := by
      congr 1; funext x; apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := integral_finset_sum _ (fun j _ => hi j)

private theorem continuous_weakTimeFunctional {d : ℕ} (i : Fin d) (ζ : ℂ) (n : ℕ)
    (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ)
    (ω : FieldPair d)
    (hU : ∀ K : Set (Vec d), IsCompact K → Integrable
      (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (hV : ∀ k K, IsCompact K → Integrable
      (fun p : Vec d × ℝ => V k (p.2, translate p.1 ω))
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Continuous (weakTimeFunctional i ζ n U V ω φ) := by
  have hφr : Continuous (fun x => (φ x : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hφrc : HasCompactSupport (fun x => (φ x : ℂ)) := hφc.comp_left (g := Complex.ofReal) rfl
  have hleft := (continuous_spatial_temporal_pairing hU hφr hφrc
    (measurable_clampTime n)).comp (continuous_snd : Continuous (Prod.snd : TimeJet n → _))
  have hprincipal := continuous_principal_time_pairing n V ω hV φ hφ hφc
  have hdrift := continuous_drift_time_pairing i n V ω hV φ hφ.continuous hφc
  exact (hleft.sub (continuous_const.mul hprincipal)).add (continuous_const.mul hdrift)

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Actual joint orbit/gradient representatives satisfy the weak equation on
one event before all C1 temporal tests and smooth compact spatial tests, on
every integer window. Only local space-time L1 is used at time zero. -/
theorem IsComplexEnvironmentSemigroup.exists_joint_weak_time_equation_all_tests
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ,
        (∀ K : Set (Vec d), IsCompact K →
          Integrable (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
          ∀ j, Integrable (fun p : Vec d × ℝ => V j (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
        ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
          η 0 = 0 → η n = 0 →
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) := by
  obtain ⟨U, V, hU, hV, heU, heV, he⟩ :=
    hP.exists_joint_weak_time_equation_all_spatial_tests f
  have hlU (n : ℕ) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative
      (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (n : ℝ)) hU heU)
  have hlV (n : ℕ) (j : Fin d) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
        (hP.integrableOn_gradientOrbit f (n : ℝ≥0))) (hV j) (heV j))
  let Test := {φ : Vec d → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  have hall (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q, ∀ q ∈ c1Jets n, ∀ φ : Test,
      weakTimeFunctional i ζ n U V ω φ.1 q = 0 := by
    apply ae_all_parameters_of_ae_fixed (reducedLaw Q) (c1Jets n)
      (fun ω (φ : Test) q => weakTimeFunctional i ζ n U V ω φ.1 q)
    · filter_upwards [hlU n, ae_all_iff.mpr (hlV n)] with ω hu hv
      intro φ
      exact (continuous_weakTimeFunctional i ζ n U V ω hu hv φ.1 φ.2.1 φ.2.2).comp
        continuous_subtype_val
    · rintro q ⟨η, η', hη, hη', hzero, ht, rfl⟩
      filter_upwards [he η η' hη hη' (n : ℝ≥0) hzero ht] with ω hω
      intro φ
      have heq := hω φ.1 φ.2.1 φ.2.2
      dsimp only [weakTimeFunctional, Prod.fst, Prod.snd]
      simp_rw [integral_restrictTime]
      simp only [NNReal.coe_natCast] at heq
      linear_combination heq
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  filter_upwards [ae_all_iff.mpr hlU,
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (hlV n)), ae_all_iff.mpr hall] with ω hu hv heq
  intro n
  refine ⟨fun K hK => ⟨hu n K hK, fun j => hv n j K hK⟩, ?_⟩
  intro η η' hη hη' hzero ht φ hφ hφc
  have he := heq n
    (restrictTime n η (continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt),
      restrictTime n η' hη') ⟨η, η', hη, hη', hzero, ht, rfl⟩ (⟨φ, hφ, hφc⟩ : Test)
  dsimp only [weakTimeFunctional, Prod.fst, Prod.snd] at he
  simp_rw [integral_restrictTime] at he
  linear_combination he

/-- The constructed signed-complex evolution supplies every semigroup,
representative and local-integrability producer internally. Its common event
precedes every temporal test and every spatial test on all integer windows. -/
theorem forcedComplexEvolution_exists_joint_weak_time_equation_all_tests
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] forcedComplexEvolution Q i ζ s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ,
        (∀ K : Set (Vec d), IsCompact K →
          Integrable (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
          ∀ j, Integrable (fun p : Vec d × ℝ => V j (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
        ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
          η 0 = 0 → η n = 0 →
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).exists_joint_weak_time_equation_all_tests f

end EinsteinFull
