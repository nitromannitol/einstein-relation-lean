import EinsteinFull.Calculus.C3PhysicalTransposeDualGraph
import EinsteinFull.Calculus.C3PhysicalBilinearTranspose
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
private def C0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

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

private def pairR {d : ℕ} (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ := innerSL ℂ (physicalConj u)

private theorem pairR_apply {d : ℕ} (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    pairR u v = ∫ x, u x * v x := (physical_pairing_eq_inner u v).symm

private theorem pairR_comm {d : ℕ} (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    pairR u v = pairR v u := by
  simp only [pairR_apply]
  congr 1
  ext x
  exact mul_comm _ _

/-- Bilinear duality with a physical forward C0 semigroup identifies the full transpose graph. -/
theorem physical_complex_transpose_semigroup_of_forward
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT0 : T 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure (Vec d))))
    (hTm : ∀ s t : ℝ≥0, T (s+t) = (T s).comp (T t))
    (hTc : ∀ f : Lp ℂ 2 (volume : Measure (Vec d)), Continuous (fun t : ℝ≥0 => T t f))
    (hdual : ∀ (t : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x : Vec d, (P t f) x * g x) = ∫ x : Vec d, f x * (T t g) x) :
    IsPhysicalComplexTransposeSemigroup a i ζ P T := by
  let p := fun t : ℝ≥0 => (P t).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) hP.1
  have hpm : ∀ s t, p (s + t) = (p s).comp (p t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) (hP.2.1 s t)
  have hpc : ∀ f, Continuous (fun t => p t f) := hP.2.2.1
  have hdual' (t : ℝ≥0) (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
      pairR u (T t v) = pairR v (P t u) := by
    rw [pairR_apply, ← hdual, ← pairR_apply, pairR_comm]
  refine ⟨hT0, hTm, hTc, ?_, hdual⟩
  intro f g
  rw [physical_complex_transpose_generator_iff_dual a i ζ ha hΛ hA f g]
  constructor
  · intro hfg u v huv
    have huv' := (hP.2.2.2 u v).mpr huv
    have hl := ((pairR u).continuous.tendsto g).comp hfg
    have hr := ((pairR f).continuous.tendsto v).comp huv'
    have he (t : ℝ≥0) :
        pairR u (((t : ℝ) : ℂ)⁻¹ • (T t f - f)) =
          pairR f (((t : ℝ) : ℂ)⁻¹ • (P t u - u)) := by
      simp only [map_smul, map_sub, hdual', pairR_comm u f]
    have hh : pairR u g = pairR f v := tendsto_nhds_unique (hl.congr (fun t => he t)) hr
    simpa only [pairR_apply, mul_comm] using hh.symm
  · intro hweak
    have hint (t : ℝ≥0) :
        (∫ s in (0 : ℝ)..(t : ℝ), T s.toNNReal g) = T t f - f := by
      apply ext_inner_left ℂ
      intro z
      let u := physicalConj z
      have hconj : physicalConj u = z := by
        apply Lp.ext
        filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (p := 2) z,
          Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (p := 2) u] with x hx hy
        change physicalConj u x = star (u x) at hy
        change u x = star (z x) at hx
        rw [hy, hx, star_star]
      change inner ℂ z _ = inner ℂ z _
      rw [← hconj]
      change pairR u _ = pairR u _
      have hTi : IntervalIntegrable (fun s : ℝ => T s.toNNReal g) volume 0 (t : ℝ) :=
        ((hTc g).comp continuous_real_toNNReal).intervalIntegrable 0 t
      rw [← (pairR u).intervalIntegral_comp_comm hTi]
      have hw := hweak (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) (P t u - u)
        ((hP.2.2.2 _ _).mp (c0Graph_complex_iff.mp
          (c0Graph_integral hp0 hpm hpc u t)))
      rw [← pairR_apply, ← pairR_apply] at hw
      calc
        (∫ s in (0 : ℝ)..(t : ℝ), pairR u (T s.toNNReal g)) =
            ∫ s in (0 : ℝ)..(t : ℝ), pairR g (P s.toNNReal u) := by
          apply intervalIntegral.integral_congr
          intro s _
          exact hdual' s.toNNReal u g
        _ = pairR g (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) :=
          (pairR g).intervalIntegral_comp_comm
            (((hP.2.2.1 u).comp continuous_real_toNNReal).intervalIntegrable 0 t)
        _ = pairR (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) g := pairR_comm _ _
        _ = pairR (P t u - u) f := hw.symm
        _ = pairR u (T t f - f) := by
          rw [pairR_comm (P t u - u) f]
          simp only [map_sub, hdual', pairR_comm u f]
    have hc := ((hTc g).comp continuous_real_toNNReal).integral_hasStrictDerivAt 0 0
    have hd := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
      (hc.hasDerivAt.hasDerivWithinAt (s := Ioi 0))
    have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ))
        (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
      simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
        (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
          (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
    have hh := hd.comp hcoe
    have h0 : T 0 g = g := congrArg (fun A => A g) hT0
    apply c0Graph_complex_iff.mp
    change Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t f - f)) _ _
    simpa only [Function.comp_def, slope_def_module, sub_zero,
      intervalIntegral.integral_same, Real.toNNReal_zero, h0, hint] using hh

end EinsteinFull.Blueprint
