import EinsteinFull.Calculus.PhysicalComplexEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The two physical weak graphs are transposes for the literal bilinear dx pairing. -/
theorem physical_complex_generator_bilinear
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f Af g Ag : Lp ℂ 2 (volume : Measure (Vec d))}
    (hf : IsPhysicalComplexGeneratorPair a i ζ f Af)
    (hg : IsPhysicalComplexTransposeGeneratorPair a i ζ g Ag) :
    (∫ x, Af x * g x) = ∫ x, f x * Ag x := by
  obtain ⟨Gf, hGf, hf⟩ := hf
  obtain ⟨Gg, hGg, hg⟩ := hg
  rw [hf g Gg hGg]
  have he : (∫ x, f x * Ag x) = ∫ x, Ag x * f x := by
    congr 1
    ext x
    exact mul_comm _ _
  rw [he, hg f Gf hGf]
  congr 2
  · congr 1
    ext x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · congr 1
    ext x
    ring

private def C0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem C0Graph.map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E} (hfg : C0Graph P f g) (t : ℝ≥0) :
    C0Graph P (P t f) (P t g) := by
  change Tendsto _ _ _
  have h := ((P t).continuous.tendsto g).comp hfg
  convert h using 1
  ext s
  simp only [Function.comp_apply, map_smul, map_sub]
  have hc : P t (P s f) = P s (P t f) := by
    rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm, hPm,
      ContinuousLinearMap.comp_apply]
  rw [hc]

private theorem C0Graph.hasDerivWithinAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E} (hfg : C0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => P (Real.toNNReal s) f)
      (P (Real.toNNReal t) g) (Ici t) t := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mpr
  have he : Tendsto (fun s : ℝ => Real.toNNReal (s-t))
      (𝓝[>] t) (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def, id_eq, sub_self, Real.toNNReal_zero] using
        (continuous_real_toNNReal.comp (continuous_id.fun_sub (continuous_const (y := t)))).tendsto t
          |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  have h := (((P (Real.toNNReal t)).continuous.tendsto g).comp hfg).comp he
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change t < s at hs
  have hs0 : 0 ≤ s := ht.trans hs.le
  have ha : Real.toNNReal t + Real.toNNReal (s-t) = Real.toNNReal s := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left ht,
      max_eq_left (sub_nonneg.mpr hs.le), max_eq_left hs0]
    ring
  simp only [Function.comp_apply]
  rw [map_smul, map_sub]
  simp only [slope_def_module, Real.coe_toNNReal', max_eq_left (sub_nonneg.mpr hs.le)]
  rw [← ContinuousLinearMap.comp_apply, ← hPm, ha]

private theorem C0Graph.integral_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : C0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, P s.toNNReal g) = P t.toNNReal f - f := by
  have hf := (hPc f).comp continuous_real_toNNReal
  have hg := (hPc g).comp continuous_real_toNNReal
  simpa only [Function.comp_apply, Real.toNNReal_zero, hP0, ContinuousLinearMap.id_apply] using
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hf.continuousOn
      (fun s hs => (hfg.hasDerivWithinAt_orbit hPm s hs.1.le).Ioi_of_Ici)
      (hg.intervalIntegrable 0 t)

private theorem C0Graph.hasDerivAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : C0Graph P f g) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => P s.toNNReal f) (P t.toNNReal g) t := by
  have hd := (((hPc g).comp continuous_real_toNNReal).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd' := hd.add_const f
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact (eq_add_of_sub_eq (hfg.integral_orbit hP0 hPm hPc s hs.le).symm)

private theorem c0Graph_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    C0Graph P (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
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

private theorem C0Graph.smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E} {f g : E} (hfg : C0Graph P f g) (c : ℝ) :
    C0Graph P (c • f) (c • g) := by
  change Tendsto _ _ _
  have h := hfg.const_smul c
  convert h using 1
  ext t
  simp only [map_smul, ← smul_sub]
  exact smul_comm _ _ _

private theorem c0Graph_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) :
    Dense {f : E | ∃ g, C0Graph P f g} := by
  intro f
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hPc f).comp continuous_real_toNNReal
  have hd := (hu.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hh := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have ht : Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ •
      (∫ s in (0 : ℝ)..(h : ℝ), P s.toNNReal f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
    simpa only [Function.comp_def, slope_def_module, sub_zero,
      intervalIntegral.integral_same, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply] using hh.comp hcoe
  exact mem_closure_of_tendsto ht (.of_forall fun h =>
    ⟨(h : ℝ)⁻¹ • (P h f - f), (c0Graph_integral hP0 hPm hPc f h).smul _⟩)

private theorem c0Graph_complex_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {f g : E} :
    C0Graph (fun t => (P t).restrictScalars ℝ) f g ↔
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  simp only [C0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rfl

private def physicalConj {d : ℕ} :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

private theorem physical_pairing_eq_inner {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, f x * g x) = inner ℂ (physicalConj f) g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (p := 2) f] with x hx
  change physicalConj f x = star (f x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

/-- The physical forward and transpose generator graphs determine the bilinear
transpose pairing for their strongly continuous semigroups. -/
theorem physical_complex_bilinear_transpose_of_generators
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT0 : T 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure (Vec d))))
    (hTm : ∀ s t : ℝ≥0, T (s+t) = (T s).comp (T t))
    (hTc : ∀ f : Lp ℂ 2 (volume : Measure (Vec d)), Continuous (fun t : ℝ≥0 => T t f))
    (hTg : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (T t f-f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    IsPhysicalComplexTransposeSemigroup a i ζ P T := by
  -- The transpose graph already reverses the coefficient indices.
  let p := fun t : ℝ≥0 => (P t).restrictScalars ℝ
  let r := fun t : ℝ≥0 => (T t).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) hP.1
  have hr0 : r 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) hT0
  have hpm : ∀ s t, p (s + t) = (p s).comp (p t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) (hP.2.1 s t)
  have hrm : ∀ s t, r (s + t) = (r s).comp (r t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) (hTm s t)
  have hpc : ∀ f, Continuous (fun t => p t f) := hP.2.2.1
  have hrc : ∀ f, Continuous (fun t => r t f) := hTc
  refine ⟨hT0, hTm, hTc, hTg, ?_⟩
  intro t
  have hdom (f g : Lp ℂ 2 (volume : Measure (Vec d)))
      (hf : ∃ Af, C0Graph p f Af) (hg : ∃ Ag, C0Graph r g Ag) :
      (∫ x, P t f x * g x) = ∫ x, f x * T t g x := by
    obtain ⟨Af, hf⟩ := hf
    obtain ⟨Ag, hg⟩ := hg
    let w : ℝ → ℂ := fun s =>
      inner ℂ (physicalConj (P s.toNNReal f)) (T ((t : ℝ) - s).toNNReal g)
    have hw : Continuous w :=
      (physicalConj.continuous.comp ((hP.2.2.1 f).comp continuous_real_toNNReal)).inner
        ((hTc g).comp (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)))
    have hd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
        HasDerivWithinAt w 0 (Ioi s) s := by
      have hu := physicalConj.hasFDerivAt.comp_hasDerivAt s
        (hf.hasDerivAt_orbit hp0 hpm hpc s hs.1)
      have hv : HasDerivAt (fun u : ℝ => T ((t : ℝ) - u).toNNReal g)
          (-(T ((t : ℝ) - s).toNNReal Ag)) s := by
        simpa only [Function.comp_def, r, ContinuousLinearMap.coe_restrictScalars',
          zero_sub, one_smul, neg_one_smul] using
          (hg.hasDerivAt_orbit hr0 hrm hrc ((t : ℝ) - s) (sub_pos.mpr hs.2)).scomp s
            ((hasDerivAt_const s (t : ℝ)).sub (hasDerivAt_id s))
      have he := physical_complex_generator_bilinear
        ((hP.2.2.2 _ _).mp (c0Graph_complex_iff.mp (hf.map hpm s.toNNReal)))
        ((hTg _ _).mp (c0Graph_complex_iff.mp (hg.map hrm ((t : ℝ) - s).toNNReal)))
      rw [physical_pairing_eq_inner, physical_pairing_eq_inner] at he
      dsimp only [p, r, ContinuousLinearMap.coe_restrictScalars'] at he
      dsimp only [Function.comp_def, p, ContinuousLinearMap.coe_restrictScalars'] at hu
      have hz : inner ℂ (physicalConj (P s.toNNReal f)) (-(T ((t : ℝ) - s).toNNReal Ag)) +
          inner ℂ (physicalConj (P s.toNNReal Af)) (T ((t : ℝ) - s).toNNReal g) = 0 := by
        rw [inner_neg_right, he, neg_add_cancel]
      simpa only [w, hz] using (hu.inner ℂ hv).hasDerivWithinAt (s := Ioi s)
    have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      t.property hw.continuousOn hd (intervalIntegrable_const (a := (0 : ℝ)) (b := (t : ℝ)))
    have he' : w (t : ℝ) = w 0 := by
      dsimp only [w] at he ⊢
      simp only [intervalIntegral.integral_zero] at he
      exact sub_eq_zero.mp he.symm
    simpa only [w, sub_self, sub_zero, Real.toNNReal_zero, Real.toNNReal_coe,
      hP.1, hT0, ContinuousLinearMap.id_apply, ← physical_pairing_eq_inner] using he'
  intro f g
  have hD := c0Graph_dense hp0 hpm hpc
  have hE := c0Graph_dense hr0 hrm hrc
  have he (f : Lp ℂ 2 (volume : Measure (Vec d))) (hf : ∃ Af, C0Graph p f Af) :
      ∀ g, (∫ x, P t f x * g x) = ∫ x, f x * T t g x := by
    intro g
    apply congrFun ?_ g
    apply Continuous.ext_on hE
    · simp_rw [physical_pairing_eq_inner]
      exact continuous_const.inner continuous_id
    · simp_rw [physical_pairing_eq_inner]
      exact continuous_const.inner (T t).continuous
    · intro g hg
      exact hdom f g hf hg
  have hall : (fun f : Lp ℂ 2 (volume : Measure (Vec d)) => ∫ x, P t f x * g x) =
      (fun f => ∫ x, f x * T t g x) := by
    apply Continuous.ext_on hD
    · simp_rw [physical_pairing_eq_inner]
      exact (physicalConj.continuous.comp (P t).continuous).inner continuous_const
    · simp_rw [physical_pairing_eq_inner]
      exact physicalConj.continuous.inner continuous_const
    · intro f hf
      exact he f hf g
  exact congrFun hall f

#print axioms physical_complex_generator_bilinear
#print axioms physical_complex_bilinear_transpose_of_generators

end EinsteinFull.Blueprint
