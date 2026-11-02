import EinsteinFull.Calculus.ComplexHighExponentSupport
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Order.Bornology

/-! Strong continuity of actual higher-Lp semigroups, via higher moments and Vitali. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A uniformly bounded family in a strictly higher finite exponent is uniformly
integrable in the lower exponent. -/
theorem unifIntegrable_of_highLp_bound {ι : Type*} {f : ι → α → ℂ}
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hbound : ∀ i, eLpNorm (f i) (ENNReal.ofReal q) μ ≤ C) :
    UnifIntegrable f (ENNReal.ofReal p) μ := by
  have hq : 0 < q := hp.trans hpq
  let a := 1 / p - 1 / q
  have ha : 0 < a := sub_pos.mpr (one_div_lt_one_div_of_lt hp hpq)
  unfold UnifIntegrable
  have hlim : Tendsto (fun δ : ℝ≥0∞ => C * δ ^ a) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun δ => ?_)
  simp only [iSup_le_iff]
  intro i s hs
  calc
    eLpNorm (f i) (ENNReal.ofReal p) (μ.restrict s) ≤
        eLpNorm (f i) (ENNReal.ofReal q) (μ.restrict s) *
          (μ.restrict s) Set.univ ^ a := by
      simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, a] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hpq.le)
          (hf i).restrict
    _ ≤ C * δ ^ a := by
      apply mul_le_mul'
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hbound i)
      · apply ENNReal.rpow_le_rpow _ ha.le
        simpa only [Measure.restrict_apply_univ] using hs

/-- L2 convergence plus a uniform bound at one strictly higher exponent gives
actual Lp convergence; the stronger bound supplies Vitali uniform integrability. -/
theorem tendsto_highLp_of_L2_of_bound [IsProbabilityMeasure μ]
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp2 : 2 ≤ p) (hpq : p < q)
    {F : ℕ → Lp ℂ (ENNReal.ofReal p) μ} {g : Lp ℂ (ENNReal.ofReal p) μ}
    (hF : Tendsto (fun n => complexLpToL2 μ
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (F n)) atTop
      (𝓝 (complexLpToL2 μ (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) g)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, eLpNorm (F n) (ENNReal.ofReal q) μ ≤ C) :
    Tendsto F atTop (𝓝 g) := by
  have hm : TendstoInMeasure μ (fun n => complexLpToL2 μ
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (F n)) atTop
      (complexLpToL2 μ (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) g) :=
    tendstoInMeasure_of_tendsto_Lp hF
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F g).mpr
  exact tendsto_Lp_finite_of_tendstoInMeasure (by exact_mod_cast
    (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))) ENNReal.ofReal_ne_top
    (fun n => Lp.aestronglyMeasurable (F n)) (Lp.memLp g)
    (unifIntegrable_of_highLp_bound (by linarith) hpq hC
      (fun n => Lp.aestronglyMeasurable (F n)) hbound)
    (by simpa only [complexLpToL2_apply] using hm)

/-- Higher-moment control upgrades actual L2 continuity to continuity in Lp. -/
theorem continuous_highLp_of_L2_of_bound [IsProbabilityMeasure μ]
    {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp2 : 2 ≤ p) (hpq : p < q)
    (F : X → Lp ℂ (ENNReal.ofReal p) μ)
    (hF : Continuous (fun x => complexLpToL2 μ
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (F x)))
    (M : X → ℝ) (hM : Continuous M)
    (hbound : ∀ x, eLpNorm (F x) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (M x)) :
    Continuous F := by
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto (fun n => M (u n))
    ((hM.tendsto x).comp hu)).bddAbove
  exact tendsto_highLp_of_L2_of_bound hp2 hpq ((hF.tendsto x).comp hu)
    ENNReal.ofReal_ne_top (fun n => (hbound (u n)).trans
      (ENNReal.ofReal_le_ofReal (hR (Set.mem_range_self n))))

private theorem norm_exp_damped_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : F →L[ℂ] F) (a : ℝ) (hA : ‖A‖ ≤ Real.exp a) :
    ‖(Real.exp (-a) : ℂ) • A‖ ≤ 1 := by
  calc
    _ = Real.exp (-a) * ‖A‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-a) * Real.exp a := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

private theorem continuous_undamped_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (B : ℝ≥0 → F →L[ℂ] F) (c : ℝ)
    (hB : Continuous (fun ft : F × ℝ≥0 => B ft.2 ft.1)) :
    Continuous (fun tf : ℝ≥0 × F =>
      (Real.exp (c * (tf.1 : ℝ)) : ℂ) • B tf.1 tf.2) := by
  have hs : Continuous (fun tf : ℝ≥0 × F => (Real.exp (c * (tf.1 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul
        (NNReal.continuous_coe.comp continuous_fst)))
  exact hs.smul (hB.comp continuous_swap)


private theorem memLp_simple_high [IsProbabilityMeasure μ]
    {p q : ℝ≥0∞} (f : Lp.simpleFunc ℂ p μ) : MemLp (f : Lp ℂ p μ) q μ :=
  (memLp_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f)).mp
    (((Lp.simpleFunc.toSimpleFunc f).memLp_top μ).mono_exponent le_top)

private theorem continuous_family_of_dense_exp_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (B : ℝ≥0 → F →L[ℂ] F) (c : ℝ) (D : Set F) (hD : Dense D)
    (hcont : ∀ f ∈ D, Continuous (fun t => B t f))
    (hnorm : ∀ t, ‖B t‖ ≤ Real.exp (c * (t : ℝ))) :
    Continuous (fun tf : ℝ≥0 × F => B tf.1 tf.2) := by
  let E (t : ℝ≥0) := (Real.exp (-(c * (t : ℝ))) : ℂ) • B t
  have hE : Continuous (fun ft : F × ℝ≥0 => E ft.2 ft.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hD
    · intro f hf
      exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul NNReal.continuous_coe).neg))).smul
          (hcont f hf)
    · intro t
      exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (f := E t) (K := 1)
        (norm_exp_damped_le (B t) _ (hnorm t))
  have hc := continuous_undamped_family E c hE
  convert hc using 1
  funext tf
  simp only [E, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_smul]

/-- Actual L2 continuity and proved higher-moment growth give joint Lp continuity. -/
theorem continuous_complexLp_restriction_of_exp_bound [IsProbabilityMeasure μ]
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp2 : 2 ≤ p) (hpq : p < q)
    (B : ℝ≥0 → Lp ℂ (ENNReal.ofReal p) μ →L[ℂ] Lp ℂ (ENNReal.ofReal p) μ)
    (c cq : ℝ)
    (hcont : ∀ f, Continuous (fun t => complexLpToL2 μ
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (B t f)))
    (hnorm : ∀ t, ‖B t‖ ≤ Real.exp (c * (t : ℝ)))
    (hbound : ∀ f : Lp ℂ (ENNReal.ofReal p) μ,
      MemLp f (ENNReal.ofReal q) μ → ∀ t,
      eLpNorm (B t f) (ENNReal.ofReal q) μ ≤ eLpNorm f (ENNReal.ofReal q) μ *
        ENNReal.ofReal (Real.exp (cq * (t : ℝ)))) :
    Continuous (fun tf : ℝ≥0 × Lp ℂ (ENNReal.ofReal p) μ => B tf.1 tf.2) := by
  have hsimple (f : Lp.simpleFunc ℂ (ENNReal.ofReal p) μ) :
      Continuous (fun t => B t f) := by
    have hf : MemLp (f : Lp ℂ (ENNReal.ofReal p) μ) (ENNReal.ofReal q) μ :=
      memLp_simple_high f
    apply continuous_highLp_of_L2_of_bound hp2 hpq _ (hcont f)
      (fun t => (eLpNorm (f : Lp ℂ (ENNReal.ofReal p) μ) (ENNReal.ofReal q) μ).toReal *
        Real.exp (cq * (t : ℝ)))
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul NNReal.continuous_coe)))
    intro t
    simpa only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hf.eLpNorm_ne_top] using hbound f hf t
  exact continuous_family_of_dense_exp_bound B c _
    (Lp.simpleFunc.dense (E := ℂ) (μ := μ) ENNReal.ofReal_ne_top)
    (fun f hf => hsimple ⟨f, hf⟩) hnorm


section Physical
variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {p : ℝ} (hp2 : 2 ≤ p)

/-- The actual forward higher-Lp action is jointly continuous in time and data. -/
theorem IsComplexEnvironmentSemigroup.continuous_lpRestriction
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    Continuous (fun tf : ℝ≥0 × Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) =>
      hP.lpRestriction hp2 tf.1 tf.2) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  apply continuous_complexLp_restriction_of_exp_bound hp2 (q := p + 1) (by linarith)
    (hP.lpRestriction hp2)
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) * (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) * (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)
  · intro f
    simpa only [hP.lpRestriction_apply hp2] using
      hP.2.2.1 (complexLpToL2 (reducedLaw Q)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) f)
  · exact hP.norm_lpRestriction_le hp2
  · intro f hf t
    have hb := (hP.highLp_bound (show 2 ≤ p + 1 by linarith)
      (complexLpToL2 (reducedLaw Q)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) f) hf t).2
    simpa only [← hP.lpRestriction_apply hp2 t f, complexLpToL2_apply] using hb

/-- The actual transpose higher-Lp action is jointly continuous in time and data. -/
theorem IsComplexTransposeSemigroup.continuous_lpRestriction
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    Continuous (fun tf : ℝ≥0 × Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) =>
      hT.lpRestriction hp2 hP tf.1 tf.2) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  apply continuous_complexLp_restriction_of_exp_bound hp2 (q := p + 1) (by linarith)
    (hT.lpRestriction hp2 hP)
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) * (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (p - 1)) ^ 2)
    ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) * (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (p + 1 - 1)) ^ 2)
  · intro f
    simpa only [hT.lpRestriction_apply hp2 hP] using
      hT.continuous_apply hP (complexLpToL2 (reducedLaw Q)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) f)
  · exact hT.norm_lpRestriction_le hp2 hP
  · intro f hf t
    have hb := (hT.highLp_bound hP (show 2 ≤ p + 1 by linarith)
      (complexLpToL2 (reducedLaw Q)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) f) hf t).2
    simpa only [← hT.lpRestriction_apply hp2 hP t f, complexLpToL2_apply] using hb

/-- Every actual forward family gives a genuine C0 semigroup on all higher Lp. -/
theorem IsComplexEnvironmentSemigroup.lpRestriction_c0
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    hP.lpRestriction hp2 0 = ContinuousLinearMap.id ℂ _ ∧
    (∀ s t, hP.lpRestriction hp2 (s+t) =
      (hP.lpRestriction hp2 s).comp (hP.lpRestriction hp2 t)) ∧
    ∀ f, Continuous (fun t => hP.lpRestriction hp2 t f) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  exact ⟨(hP.lpRestriction_laws hp2).1, (hP.lpRestriction_laws hp2).2,
    fun f => (hP.continuous_lpRestriction hp2).comp (continuous_id.prodMk continuous_const)⟩

/-- Every actual bilinear transpose gives a genuine C0 semigroup on all higher Lp. -/
theorem IsComplexTransposeSemigroup.lpRestriction_c0
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    hT.lpRestriction hp2 hP 0 = ContinuousLinearMap.id ℂ _ ∧
    (∀ s t, hT.lpRestriction hp2 hP (s+t) =
      (hT.lpRestriction hp2 hP s).comp (hT.lpRestriction hp2 hP t)) ∧
    ∀ f, Continuous (fun t => hT.lpRestriction hp2 hP t f) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  exact ⟨(hT.lpRestriction_laws hp2 hP).1, (hT.lpRestriction_laws hp2 hP).2,
    fun f => (hT.continuous_lpRestriction hp2 hP).comp (continuous_id.prodMk continuous_const)⟩
end Physical

end EinsteinFull
