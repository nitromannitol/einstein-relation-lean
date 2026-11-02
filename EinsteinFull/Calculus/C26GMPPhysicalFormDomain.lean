import EinsteinFull.Calculus.C8FoundationGMPAssociation

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open MarkovProcess.Semigroup

/-- Every normalized orbit integral belongs to the physical form domain. -/
theorem gmpPhysicalSemigroup_orbitAverage_mem_formDomain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) :
    (t : ℝ)⁻¹ • (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).orbitIntegral f t ∈
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hu : (t : ℝ)⁻¹ • S.orbitIntegral f t ∈ S.generatorDomain :=
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f t)
  exact (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr
    (gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω ⟨_, hu⟩)

/-- Closedness transfers a uniform bound on the energies of orbit averages to
membership of the limiting datum in the full form domain. -/
theorem gmpPhysicalSemigroup_h1_of_orbitAverage_energy_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (C : ℝ)
    (hC : ∀ t : ℝ≥0, 0 < t →
      let u := (t : ℝ)⁻¹ • (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).orbitIntegral f t
      u ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain ∧
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form u u ≤ C) :
    physicalH1Member ω hd lam f := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hclosed : IsClosed {u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
      u ∈ E.domain ∧ E.form u u ≤ C} := by
    apply IsSeqClosed.isClosed
    intro us u hus hlim
    exact E.mem_domain_of_tendsto_of_form_le (fun n => (hus n).1) hlim
      (fun n => (hus n).2)
  have hmem : f ∈ {u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
      u ∈ E.domain ∧ E.form u u ≤ C} := by
    apply hclosed.mem_of_tendsto (S.tendsto_inv_smul_orbitIntegral f)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hC t ht
  exact (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mp hmem.1

/-- Full-domain data have uniformly bounded difference quotients at every
positive time. -/
theorem gmpPhysicalSemigroup_formQuotient_bounded_of_h1 {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : physicalH1Member ω hd lam f) :
    ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ)⁻¹ * inner ℝ (f - (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) f ≤ C := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let q : ℝ≥0 → ℝ := fun t => (t : ℝ)⁻¹ * inner ℝ (f - S t f) f
  have hlim : Tendsto q (𝓝[Set.Ioi 0] 0) (𝓝 (E.form f f)) :=
    gmpPhysicalSemigroup_formLimit hd ω lam Λ hΛ hω hf hf
  have hev : ∀ᶠ t in 𝓝[Set.Ioi 0] (0 : ℝ≥0), q t < E.form f f + 1 :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨v, hv, hvsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨max (E.form f f + 1) (ε⁻¹ * (2 * ‖f‖ * ‖f‖)), ?_⟩
  intro t ht
  by_cases hsmall : (t : ℝ) < ε
  · have htv : t ∈ v := hεv (by simpa only [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      (abs_of_nonneg t.coe_nonneg)] using hsmall)
    exact (hvsub ⟨htv, ht⟩).le.trans (le_max_left _ _)
  · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
    have hinv : (t : ℝ)⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ htpos hε).mpr (le_of_not_gt hsmall)
    have hinner : inner ℝ (f - S t f) f ≤ 2 * ‖f‖ * ‖f‖ := by
      calc
        _ ≤ ‖f - S t f‖ * ‖f‖ := real_inner_le_norm _ _
        _ ≤ (‖f‖ + ‖S t f‖) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
        _ ≤ (‖f‖ + ‖f‖) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (add_le_add_right (S.norm_apply_le t f) _) (norm_nonneg _)
        _ = 2 * ‖f‖ * ‖f‖ := by ring
    have hbound : q t ≤ ε⁻¹ * (2 * ‖f‖ * ‖f‖) := by
      calc
        _ ≤ (t : ℝ)⁻¹ * (2 * ‖f‖ * ‖f‖) :=
          mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr htpos.le)
        _ ≤ ε⁻¹ * (2 * ‖f‖ * ‖f‖) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
    exact hbound.trans (le_max_right _ _)

/-- A bound on the form quotients gives full-domain membership once the
orbit-average energy estimate is available. -/
theorem gmpPhysicalSemigroup_h1_of_bounded_formQuotient_of_orbit_energy
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hB8f : ∀ t : ℝ≥0, 0 < t →
      let u := (t : ℝ)⁻¹ •
        (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).orbitIntegral f t
      u ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain ∧
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form u u ≤
        (t : ℝ)⁻¹ * inner ℝ
          (f - (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) f)
    (hbound : ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ)⁻¹ * inner ℝ
        (f - (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) f ≤ C) :
    physicalH1Member ω hd lam f := by
  obtain ⟨C, hC⟩ := hbound
  apply gmpPhysicalSemigroup_h1_of_orbitAverage_energy_bound hd ω lam Λ hΛ hω f C
  intro t ht
  exact ⟨(hB8f t ht).1, (hB8f t ht).2.trans (hC t ht)⟩

/-- The physical form domain is exactly the set of L² data with bounded
semigroup difference quotients. -/
theorem gmpPhysicalSemigroup_bounded_formQuotient_iff {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ((∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ)⁻¹ * inner ℝ (f - (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) f ≤ C) ↔
      physicalH1Member ω hd lam f) := by
  constructor
  · intro hbound
    apply gmpPhysicalSemigroup_h1_of_bounded_formQuotient_of_orbit_energy
      hd ω lam Λ hΛ hω f
    · intro t ht
      exact ⟨gmpPhysicalSemigroup_orbitAverage_mem_formDomain hd ω lam Λ hΛ hω f t,
        gmpPhysicalSemigroup_orbitAverage_energy_le_differenceQuotient
          hd ω lam Λ hΛ hω f t ht⟩
    · exact hbound
  · exact gmpPhysicalSemigroup_formQuotient_bounded_of_h1 hd ω lam Λ hΛ hω f

end EinsteinFull.Blueprint
