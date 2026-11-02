import EinsteinFull.Calculus.U4PhysicalWeightedNash

open MeasureTheory
open scoped ENNReal
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

noncomputable section
namespace EinsteinFull

/-- At zero force the physical weak-gradient graph has the same representative in
ordinary spatial H¹. -/
def u4UnforcedPhysicalGraphToSpatialH1 {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0)) :
    PDE.H1Function (Set.univ : Set (Vec d)) where
  toFun := u.value
  grad := fun x => WithLp.ofLp (u.weakGradient x)
  memL2 := by
    simpa only [PDE.MemL2On, PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using
      u.value_memLp.of_measure_le_smul (c := ENNReal.ofReal (Real.exp (2 * Λ)))
        ENNReal.ofReal_ne_top (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  gradMemL2 i := by
    simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using
      (Blueprint.gmpEuclideanMemLp_coordinate u.gradient_memLp i).of_measure_le_smul
        (c := ENNReal.ofReal (Real.exp (2 * Λ))) ENNReal.ofReal_ne_top
        (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  hasWeakGradient := Blueprint.gmpHasWeakGradient_toPDE u.distributionalGradient

/-- Spatial Nash inequality applied to the literal physical graph representative. -/
theorem u4_unforced_physical_graph_nash {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0),
        Integrable u.value volume →
        (∫ x, u.value x ^ 2) ≤
          C * (∫ x, PDE.vecEuclideanNorm (WithLp.ofLp (u.weakGradient x)) ^ 2) ^
              ((d : ℝ) / (d + 2)) *
            (∫ x, |u.value x|) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := PDE.exists_nash_constant d (by omega)
  refine ⟨C, hC, ?_⟩
  intro u hu
  exact hN (u4UnforcedPhysicalGraphToSpatialH1 hd ω Λ hω u) hu

/-- Physical graph mass is bounded by its spatial mass. -/
theorem u4_unforced_physical_graph_mass_comparison {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0)) :
    (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
      Real.exp (2 * Λ) * (∫ x, u.value x ^ 2) := by
  have hv : MemLp u.value 2 volume :=
    u.value_memLp.of_measure_le_smul (c := ENNReal.ofReal (Real.exp (2 * Λ)))
      ENNReal.ofReal_ne_top (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  have hi : Integrable (fun x => u.value x ^ 2) volume := by
    refine (hv.integrable_norm_pow (by norm_num : 2 ≠ 0)).congr ?_
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, sq_abs]
  exact integral_le_const_mul_of_measure_le (physicalReversibleMeasure ω hd 0) volume
    (Real.exp (2 * Λ)) (Real.exp_pos _).le
    (u4_unforced_physical_measure_comparable hd ω Λ hω).1
    (fun x => u.value x ^ 2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hi

/-- Nash inequality for the literal unforced physical form and reversible measure. -/
theorem u4_unforced_physical_weighted_nash
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : EinsteinRelation.SpatialDirichlet.WeightedSobolevGraph
        (physicalReversibleMeasure ω hd 0),
      Integrable u.value (physicalReversibleMeasure ω hd 0) →
      (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
        C * (∫ x, EinsteinRelation.SpatialDirichlet.weightedFormIntegrand ω.1 u u x
          ∂physicalReversibleMeasure ω hd 0) ^ ((d : ℝ) / (d + 2)) *
        (∫ x, |u.value x| ∂physicalReversibleMeasure ω hd 0) ^
          ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u4_unforced_physical_graph_nash hd ω Λ hω
  let K := Real.exp (2 * Λ)
  let a : ℝ := (d : ℝ) / (d + 2)
  let b : ℝ := 4 / (d + 2)
  have hK : 0 < K := Real.exp_pos _
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨K * C * (K * (2 * Λ)) ^ a * K ^ b, by positivity, ?_⟩
  intro u hu
  have hL := u4_unforced_physical_integral_abs_comparison hd ω Λ hω u.value hu
  have hNash := hN u hL.1
  have hg0 : 0 ≤ ∫ x, ‖u.weakGradient x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hl0 : 0 ≤ ∫ x, |u.value x| := integral_nonneg fun x => abs_nonneg _
  have he0 : 0 ≤ ∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0 := by
    have h := u4_physical_graph_energy_lower hd ω Λ hΛ hω u
    have hg : 0 ≤ ∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd 0 :=
      integral_nonneg fun x => sq_nonneg _
    exact (mul_nonneg (by positivity) hg).trans h
  have hgrad := u4_unforced_physical_graph_spatial_gradient_le_energy hd ω Λ hΛ hω u
  have hn (x : Vec d) : PDE.vecEuclideanNorm (WithLp.ofLp (u.weakGradient x)) =
      ‖u.weakGradient x‖ := by
    change euclideanNorm (WithLp.ofLp (u.weakGradient x)) = _
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
  simp_rw [hn] at hNash
  have hp := Real.rpow_le_rpow hg0 hgrad ha
  have hq := Real.rpow_le_rpow hl0 hL.2 hb
  have hright : 0 ≤ ((K * (2 * Λ)) *
      (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0)) ^ a :=
    Real.rpow_nonneg (mul_nonneg (by positivity) he0) _
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hq
    (Real.rpow_nonneg hl0 _) (mul_nonneg hC.le hright)
  calc
    _ ≤ K * (∫ x, u.value x ^ 2) :=
      u4_unforced_physical_graph_mass_comparison hd ω Λ hω u
    _ ≤ K * (C * (∫ x, ‖u.weakGradient x‖ ^ 2) ^ a *
        (∫ x, |u.value x|) ^ b) := mul_le_mul_of_nonneg_left hNash hK.le
    _ ≤ K * (C * ((K * (2 * Λ)) *
        (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0)) ^ a *
        (K * (∫ x, |u.value x| ∂physicalReversibleMeasure ω hd 0)) ^ b) :=
      mul_le_mul_of_nonneg_left hprod hK.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ K * (2 * Λ)) he0,
        Real.mul_rpow hK.le (integral_nonneg fun x => abs_nonneg _)]
      ring

/-- The physical Nash estimate with the Lebesgue L¹ norm. -/
theorem u4_unforced_physical_weighted_nash_volume_L1
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : EinsteinRelation.SpatialDirichlet.WeightedSobolevGraph
        (physicalReversibleMeasure ω hd 0),
      Integrable u.value volume →
      (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
        C * (∫ x, EinsteinRelation.SpatialDirichlet.weightedFormIntegrand ω.1 u u x
          ∂physicalReversibleMeasure ω hd 0) ^ ((d : ℝ) / (d + 2)) *
        (∫ x, |u.value x|) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u4_unforced_physical_graph_nash hd ω Λ hω
  let K := Real.exp (2 * Λ)
  let a : ℝ := (d : ℝ) / (d + 2)
  let b : ℝ := 4 / (d + 2)
  have hK : 0 < K := Real.exp_pos _
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨K * C * (K * (2 * Λ)) ^ a, by positivity, ?_⟩
  intro u hu
  have hNash := hN u hu
  have hg0 : 0 ≤ ∫ x, ‖u.weakGradient x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have he0 : 0 ≤ ∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0 := by
    have h := u4_physical_graph_energy_lower hd ω Λ hΛ hω u
    have hg : 0 ≤ ∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd 0 :=
      integral_nonneg fun x => sq_nonneg _
    exact (mul_nonneg (by positivity) hg).trans h
  have hgrad := u4_unforced_physical_graph_spatial_gradient_le_energy hd ω Λ hΛ hω u
  have hn (x : Vec d) : PDE.vecEuclideanNorm (WithLp.ofLp (u.weakGradient x)) =
      ‖u.weakGradient x‖ := by
    change euclideanNorm (WithLp.ofLp (u.weakGradient x)) = _
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
  simp_rw [hn] at hNash
  have hp := Real.rpow_le_rpow hg0 hgrad ha
  calc
    _ ≤ K * (∫ x, u.value x ^ 2) :=
      u4_unforced_physical_graph_mass_comparison hd ω Λ hω u
    _ ≤ K * (C * (∫ x, ‖u.weakGradient x‖ ^ 2) ^ a *
        (∫ x, |u.value x|) ^ b) := mul_le_mul_of_nonneg_left hNash hK.le
    _ ≤ K * (C * ((K * (2 * Λ)) *
        (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0)) ^ a *
        (∫ x, |u.value x|) ^ b) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ K * (2 * Λ)) he0]
      ring

/-- The weighted Nash inequality on the actual closed physical form domain. -/
theorem u4_unforced_physical_closedForm_nash
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0),
      physicalH1Member ω hd 0 f →
      Integrable (f : Vec d → ℝ) (physicalReversibleMeasure ω hd 0) →
      (∫ x, f x ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
        C * ((Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form f f) ^
          ((d : ℝ) / (d + 2)) *
        (∫ x, |f x| ∂physicalReversibleMeasure ω hd 0) ^
          ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u4_unforced_physical_weighted_nash hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf hi
  obtain ⟨v, rfl⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω 0 Λ hω f).mpr hf
  let g : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0) :=
    sourcePhysicalGraph (sourceReducedDensity hd 0)
      (continuousSourceReducedDensity hd 0) (positiveSourceReducedDensity hd 0)
      (sourcePhysicalDensity ω hd 0) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd 0 Λ hω) v
  have hv : g.value =ᵐ[physicalReversibleMeasure ω hd 0]
      (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v : Vec d → ℝ) := by
    exact g.value_memLp.coeFn_toLp.symm
  have hn := hN g (hi.congr hv.symm)
  have hm : (∫ x, g.value x ^ 2 ∂physicalReversibleMeasure ω hd 0) =
      ∫ x, (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v) x ^ 2
        ∂physicalReversibleMeasure ω hd 0 := by
    exact integral_congr_ae (hv.mono fun x hx => by simpa only using congrArg (fun t : ℝ => t ^ 2) hx)
  have hL : (∫ x, |g.value x| ∂physicalReversibleMeasure ω hd 0) =
      ∫ x, |(Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v) x|
        ∂physicalReversibleMeasure ω hd 0 := by
    exact integral_congr_ae (hv.mono fun x hx => by simpa only using congrArg (fun t : ℝ => |t|) hx)
  have he : (∫ x, weightedFormIntegrand ω.1 g g x ∂physicalReversibleMeasure ω hd 0) =
      (Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form
        (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v)
        (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v) := by
    rw [Blueprint.gmpPhysicalClosedForm_value]
    rfl
  simpa only [hm, hL, he] using hn

/-- The same estimate for the literal representative of the closed form. -/
theorem u4_unforced_physical_closedForm_nash_volume_L1
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0),
      physicalH1Member ω hd 0 f →
      Integrable (f : Vec d → ℝ) volume →
      (∫ x, f x ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
        C * ((Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form f f) ^
          ((d : ℝ) / (d + 2)) *
        (∫ x, |f x|) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u4_unforced_physical_weighted_nash_volume_L1 hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf hi
  obtain ⟨v, rfl⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω 0 Λ hω f).mpr hf
  let g : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0) :=
    sourcePhysicalGraph (sourceReducedDensity hd 0)
      (continuousSourceReducedDensity hd 0) (positiveSourceReducedDensity hd 0)
      (sourcePhysicalDensity ω hd 0) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd 0 Λ hω) v
  have hv : g.value =ᵐ[physicalReversibleMeasure ω hd 0]
      (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v : Vec d → ℝ) :=
    g.value_memLp.coeFn_toLp.symm
  have hvVol := (Measure.absolutelyContinuous_of_le_smul
    (u4_unforced_physical_measure_comparable hd ω Λ hω).2).ae_eq hv
  have hn := hN g (hi.congr hvVol.symm)
  have hm : (∫ x, g.value x ^ 2 ∂physicalReversibleMeasure ω hd 0) =
      ∫ x, (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v) x ^ 2
        ∂physicalReversibleMeasure ω hd 0 := by
    exact integral_congr_ae (hv.mono fun x hx => by simpa only using congrArg (fun t : ℝ => t ^ 2) hx)
  have hL : (∫ x, |g.value x|) =
      ∫ x, |(Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v) x| := by
    exact integral_congr_ae (hvVol.mono fun x hx => by simpa only using congrArg (fun t : ℝ => |t|) hx)
  have he : (∫ x, weightedFormIntegrand ω.1 g g x ∂physicalReversibleMeasure ω hd 0) =
      (Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form
        (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v)
        (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω v) := by
    rw [Blueprint.gmpPhysicalClosedForm_value]
    rfl
  simpa only [hm, hL, he] using hn

/-- On the physical generator domain, the full form is its negative pairing. -/
theorem u4_unforced_physical_generator_form_identity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generatorDomain) :
    (Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form f f =
      - inner ℝ ((Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generator f) f := by
  have hf := Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω 0 Λ hΛ hω f
  have h := Blueprint.gmpPhysicalSemigroup_generator_form hd ω 0 Λ hΛ hω f f
    ((Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω 0 Λ hΛ hω f).mpr hf)
  linarith

/-- Nash inequality on the actual unforced physical generator domain. -/
theorem u4_unforced_physical_generator_nash
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    let μ := physicalReversibleMeasure ω hd 0
    let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
    ∃ C : ℝ, 0 < C ∧ ∀ f : S.generatorDomain,
      Integrable (f : Vec d → ℝ) μ →
      (∫ x, (f : Vec d → ℝ) x ^ 2 ∂μ) ≤
        C * (-inner ℝ (S.generator f) (f : Lp ℝ 2 μ)) ^ ((d : ℝ) / (d + 2)) *
          (∫ x, |(f : Vec d → ℝ) x| ∂μ) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u4_unforced_physical_closedForm_nash hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf
  have h := hN f
    (Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω 0 Λ hΛ hω f) hf
  rw [u4_unforced_physical_generator_form_identity hd ω Λ hΛ hω f] at h
  exact h

#print axioms u4_unforced_physical_generator_nash
#print axioms u4_unforced_physical_generator_form_identity
#print axioms u4_unforced_physical_closedForm_nash_volume_L1
#print axioms u4_unforced_physical_weighted_nash_volume_L1
#print axioms u4_unforced_physical_weighted_nash
#print axioms u4_unforced_physical_closedForm_nash

end EinsteinFull
