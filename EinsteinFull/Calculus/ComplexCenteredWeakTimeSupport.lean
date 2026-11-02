import EinsteinFull.Calculus.ComplexCenteringSourceSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport

/-!
# A common weak-time equation for the actual centered orbit

The jointly measurable field is centered by its actual stationary mean.
Product integrability justifies subtracting that mean inside both integrals.
The scalar mean balance then gives the literal centering source with a plus
sign in the temporally tested equation. The event precedes all separated tests.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation CommonTemporalTests

private theorem integral_sub_temporal_constant {d : ℕ} {ν : Measure ℝ} [SFinite ν]
    {F : Vec d × ℝ → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K → Integrable F ((volume.restrict K).prod ν))
    {m : ℝ → ℂ} (hm : Integrable m ν)
    {φ : Vec d → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {η : ℝ → ℝ} (hη : Measurable η) {C : ℝ} (hC : ∀ s, ‖η s‖ ≤ C) :
    (∫ x, (∫ s, (η s : ℂ) * (F (x, s) - m s) ∂ν) * φ x) =
      (∫ x, (∫ s, (η s : ℂ) * F (x, s) ∂ν) * φ x) -
        (∫ s, (η s : ℂ) * m s ∂ν) * (∫ x, φ x) := by
  have hmF (K : Set (Vec d)) (hK : IsCompact K) :
      Integrable (fun p : Vec d × ℝ => m p.2) ((volume.restrict K).prod ν) := by
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    simpa only [one_mul] using (integrable_const (1 : ℂ) (μ := volume.restrict K)).mul_prod hm
  have hiF := (integrable_spatial_mul hF hφ hφc).bdd_mul
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => by simpa only [Function.comp_apply, Complex.norm_real] using hC p.2)
  have hiM := (integrable_spatial_mul hmF hφ hφc).bdd_mul
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => by simpa only [Function.comp_apply, Complex.norm_real] using hC p.2)
  change Integrable (fun p : Vec d × ℝ => (η p.2 : ℂ) * (F p * φ p.1))
    (volume.prod ν) at hiF
  change Integrable (fun p : Vec d × ℝ => (η p.2 : ℂ) * (m p.2 * φ p.1))
    (volume.prod ν) at hiM
  have hpair := spatial_temporal_pairing (fun K hK => (hF K hK).sub (hmF K hK))
    hφ hφc hη hC
  simp only [Pi.sub_apply] at hpair
  rw [hpair.2]
  have he : (fun p : Vec d × ℝ => (η p.2 : ℂ) * ((F p - m p.2) * φ p.1)) =
      (fun p => (η p.2 : ℂ) * (F p * φ p.1) - (η p.2 : ℂ) * (m p.2 * φ p.1)) := by
    funext p
    ring
  rw [he, integral_sub hiF hiM, ← (spatial_temporal_pairing hF hφ hφc hη hC).2,
    ← (spatial_temporal_pairing hmF hφ hφc hη hC).2]
  change _ - (∫ x, (∫ s, (η s : ℂ) * m s ∂ν) * φ x) = _
  rw [integral_const_mul]

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Actual centered orbit and gradient representatives, chosen before one
common environment event and all admissible separated temporal/spatial tests. -/
theorem IsComplexEnvironmentSemigroup.exists_centered_joint_weak_time_equation_all_tests
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] centeredComplexLp Q (P s.toNNReal f)) ∧
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
              (φ x : ℂ)) +
          (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * hP.centeringSource f s) *
            (∫ x : Vec d, (φ x : ℂ)) := by
  obtain ⟨U, V, hU, hV, heU, heV, he⟩ :=
    hP.exists_joint_weak_time_equation_all_tests f
  let m : ℝ → ℂ := fun s => ∫ ω, P s.toNNReal f ω ∂reducedLaw Q
  have hmc : Continuous m := (continuous_complexL2_integral (reducedLaw Q)).comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
  let W : ℝ × FieldPair d → ℂ := fun p => U p - m p.1
  have hW : Measurable W := hU.sub (hmc.measurable.comp measurable_fst)
  have heW (s : ℝ) : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      centeredComplexLp Q (P s.toNNReal f) := by
    filter_upwards [heU s, coeFn_centeredComplexLp Q (P s.toNNReal f)] with ω hu hc
    dsimp only [W, m]
    rw [hu, hc]
  have hcc : Continuous (fun t : ℝ≥0 => centeredComplexLp Q (P t f)) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp (hP.2.2.1 f)
  have hlW (n : ℕ) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative
      (integrableOn_comp_toNNReal_Icc _ hcc (n : ℝ)) hW heW)
  refine ⟨W, V, hW, hV, heW, heV, ?_⟩
  filter_upwards [he, ae_all_iff.mpr hlW] with ω hω hw
  intro n
  refine ⟨fun K hK => ⟨hw n K hK, (hω n).1 K hK |>.2⟩, ?_⟩
  intro η η' hη hη' hzero ht φ hφ hφc
  let g : ℝ → Icc (0 : ℝ) (n : ℝ) := projIcc (0 : ℝ) (n : ℝ) (by positivity)
  let w : ℝ → ℝ := fun s => η' (g s)
  have hwc : Continuous w := (hη'.comp continuous_subtype_val).comp continuous_projIcc
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hη').isBounded.exists_norm_le
  have hwb (s : ℝ) : ‖w s‖ ≤ C := hC _ ⟨g s, (g s).property, rfl⟩
  have hwint (F : ℝ → ℂ) :
      (∫ s in Icc (0 : ℝ) (n : ℝ), (w s : ℂ) * F s) =
        ∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) * F s := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [w, g, projIcc_of_mem (by positivity : (0 : ℝ) ≤ n) hs]
  have hsub := integral_sub_temporal_constant
    (fun K hK => ((hω n).1 K hK).1) (hmc.continuousOn.integrableOn_compact isCompact_Icc)
    (Complex.continuous_ofReal.comp hφ.continuous)
    (hφc.comp_left (g := Complex.ofReal) rfl) hwc.measurable hwb
  change (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (w s : ℂ) *
      (U (s, translate x ω) - m s)) * (φ x : ℂ)) = _ at hsub
  simp_rw [hwint] at hsub
  change (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
    (U (s, translate x ω) - m s)) * (φ x : ℂ)) = _
  simp only [Function.comp_apply] at hsub
  rw [hsub, (hω n).2 η η' hη hη' hzero ht φ hφ hφc]
  have hm := hP.timeTest_mean_balance f η η' hη hη' (n : ℝ≥0) hzero ht
  simp only [NNReal.coe_natCast] at hm
  change (∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) * m s) = _ at hm
  rw [hm]
  ring

/-- The constructed evolution supplies every semigroup, graph, source and
common-event producer internally for the actual centered equation. -/
theorem forcedComplexEvolution_exists_centered_joint_weak_time_equation_all_tests
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q]
        centeredComplexLp Q (forcedComplexEvolution Q i ζ s.toNNReal f)) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q]
        ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).gradientOrbit f s) j) ∧
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
              (φ x : ℂ)) +
          (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) *
            (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).centeringSource f s) *
            (∫ x : Vec d, (φ x : ℂ)) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).exists_centered_joint_weak_time_equation_all_tests f

end EinsteinFull
