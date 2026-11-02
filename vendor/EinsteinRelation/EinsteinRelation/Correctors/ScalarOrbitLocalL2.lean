import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import EinsteinRelation.Calculus.HorizontalTranslationLp

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Scalar stationary L² fields are locally L² in space almost surely;
source `paper/main.tex:693-698`. -/
theorem ae_scalar_orbit_memLp_on_all_compacts {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) := by
  have hG : Measurable f := (Lp.stronglyMeasurable f).measurable
  -- Step 1: For each n, almost surely MemLp on the closed ball of radius n+1
  have h_locally : ∀ n : ℕ, ∀ᵐ ω ∂Q,
      MemLp (fun x : Vec d => f (translate x ω)) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))) := by
    intro n
    let K : Set (Vec d) := Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
    have hK_compact : IsCompact K := isCompact_closedBall (0 : Vec d) _
    have hK_finite : volume K ≠ ⊤ := hK_compact.measure_ne_top
    letI : IsFiniteMeasure (volume.restrict K) := (isFiniteMeasure_restrict).2 hK_finite
    have hT : AEMeasurable (fun p : Vec d × FieldPair d => translate p.1 p.2)
        ((volume.restrict K).prod Q) :=
      Probability.continuous_translate.measurable.aemeasurable
    have hGmap : AEStronglyMeasurable f
        (Measure.map (fun p : Vec d × FieldPair d => translate p.1 p.2) ((volume.restrict K).prod Q)) :=
      hG.aestronglyMeasurable
    -- Prove: Measure.map (translate) (volume.restrict K × Q) = volume K • Q
    have h_map_eq : Measure.map (fun p : Vec d × FieldPair d => translate p.1 p.2)
        ((volume.restrict K).prod Q) = (volume K) • Q := by
      let T : Vec d × FieldPair d → FieldPair d := fun p => translate p.1 p.2
      have hT_meas : Measurable T := Probability.continuous_translate.measurable
      apply Measure.ext
      intro s hs
      have hsection : ∀ x : Vec d, Q {ω : FieldPair d | translate x ω ∈ s} = Q s := by
        intro x
        calc
          Q {ω : FieldPair d | translate x ω ∈ s} = Measure.map (translate x) Q s := by
            exact (Measure.map_apply (Probability.measurable_translate x) hs).symm
          _ = Q s := congrArg (fun μ : Measure (FieldPair d) => μ s) (hQ x)
      rw [Measure.map_apply hT_meas hs, Measure.prod_apply (hT_meas hs)]
      calc
        (∫⁻ x, Q {ω : FieldPair d | translate x ω ∈ s} ∂(volume.restrict K)) =
            ∫⁻ _x, Q s ∂(volume.restrict K) := by
          apply lintegral_congr
          intro x
          exact hsection x
        _ = (volume.restrict K) Set.univ * Q s := by rw [lintegral_const, mul_comm]
        _ = volume K * Q s := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        _ = ((volume K) • Q) s := by rw [Measure.smul_apply, smul_eq_mul]
    have hscaled : MemLp f 2 ((volume K) • Q) :=
      (Lp.memLp f).smul_measure (by simpa using hK_finite)
    have hmap : MemLp f 2
        (Measure.map (fun p : Vec d × FieldPair d => translate p.1 p.2) ((volume.restrict K).prod Q)) := by
      rw [h_map_eq]
      exact hscaled
    have hprod : MemLp (fun p : Vec d × FieldPair d => f (translate p.1 p.2)) 2
        ((volume.restrict K).prod Q) := by
      have hcomp := (memLp_map_measure_iff hGmap hT).1 hmap
      simpa [Function.comp_def] using! hcomp
    have hsq : Integrable (fun p : Vec d × FieldPair d =>
        ‖f (translate p.1 p.2)‖ ^ 2) ((volume.restrict K).prod Q) :=
      (memLp_two_iff_integrable_sq_norm hprod.aestronglyMeasurable).mp hprod
    have hsections := (integrable_prod_iff' hsq.aestronglyMeasurable).mp hsq
    filter_upwards [hsections.1] with ω hω
    have hmeas : AEStronglyMeasurable
        (fun x : Vec d => f (translate x ω)) (volume.restrict K) := by
      have hmeas_translate : Measurable (fun x : Vec d => translate x ω) :=
        Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)
      exact (hG.comp hmeas_translate).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
    change Integrable (fun x : Vec d => ‖f (translate x ω)‖ ^ 2) (volume.restrict K) at hω
    exact hω
  -- Step 2: Combine all n using ae_all_iff
  have h_all_n : ∀ᵐ ω ∂Q, ∀ n : ℕ,
      MemLp (fun x : Vec d => f (translate x ω)) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))) := by
    apply ae_all_iff.2
    intro n
    exact h_locally n
  -- Step 3: For any compact K, find n containing it
  filter_upwards [h_all_n] with ω hω
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hrad : R ≤ (n : ℝ) + 1 := le_trans hn.le (by norm_num)
  have hsubset : K ⊆ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall hrad)
  exact (hω n).mono_measure (Measure.restrict_mono_set volume hsubset)

end EinsteinRelation.Correctors
