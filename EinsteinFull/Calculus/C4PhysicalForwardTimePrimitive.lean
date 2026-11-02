import EinsteinFull.Calculus.C3PhysicalTransposeSemigroupGraph
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private def C4C0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem c4C0Graph_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    C4C0Graph P (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
  let u : ℝ → E := fun s => P s.toNNReal f
  let F : ℝ → E := fun s => ∫ r in (0 : ℝ)..s, u r
  have hu : Continuous u := (hPc f).comp continuous_real_toNNReal
  have hF (s : ℝ) : HasDerivAt F (u s) s :=
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hd : HasDerivAt (fun s : ℝ => F ((t : ℝ) + s) - F s) (P t f - f) 0 := by
    have h := ((hF ((t : ℝ) + 0)).scomp 0
      ((hasDerivAt_id 0).const_add (t : ℝ))).sub (hF 0)
    simp only [u, add_zero, Real.toNNReal_coe, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply, one_smul] at h
    exact h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have hh := hslope.comp hcoe
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  have hshift : P h (F (t : ℝ)) = F ((t : ℝ) + h) - F (h : ℝ) := by
    change P h (∫ s in (0 : ℝ)..(t : ℝ), u s) = _
    rw [← (P h).intervalIntegral_comp_comm (hu.intervalIntegrable 0 t)]
    have he : (fun s : ℝ => P h (u s)) =ᶠ[ae (volume.restrict (uIoc (0 : ℝ) t))]
        (fun s : ℝ => u (s + h)) := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs0 : 0 ≤ s := (min_eq_left t.property ▸ hs.1).le
      dsimp only [u]
      rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm]
      have ha : s.toNNReal + h = (s + (h : ℝ)).toNNReal := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left hs0]
        exact (max_eq_left (add_nonneg hs0 h.property)).symm
      rw [ha]
    rw [intervalIntegral.integral_congr_ae_restrict he,
      intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable 0 h) (hu.intervalIntegrable h (t + h)))
  simp only [Function.comp_apply, slope_def_module, sub_zero, add_zero, F, intervalIntegral.integral_same]
  rw [← hshift]

private theorem c4C0Graph_complex_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {f g : E} :
    C4C0Graph (fun t => (P t).restrictScalars ℝ) f g ↔
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  simp only [C4C0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rfl

/-- The time primitive of every physical L2 orbit belongs to the complete weak
physical generator graph, with generator equal to its endpoint increment. -/
theorem physical_forward_generator_timeIntegral
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    IsPhysicalComplexGeneratorPair a i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
  let p := fun s : ℝ≥0 => (P s).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg (fun A => A u) hP.1
  have hpm : ∀ s r, p (s + r) = (p s).comp (p r) := by
    intro s r
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg (fun A => A u) (hP.2.1 s r)
  have hpc : ∀ u, Continuous (fun s => p s u) := hP.2.2.1
  exact (hP.2.2.2 _ _).mp
    (c4C0Graph_complex_iff.mp (c4C0Graph_integral hp0 hpm hpc f t))

end EinsteinFull.Blueprint
